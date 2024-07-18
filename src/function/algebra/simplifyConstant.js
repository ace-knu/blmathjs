import { isFraction, isMatrix, isNode, isArrayNode, isConstantNode, isIndexNode, isObjectNode, isOperatorNode } from '../../utils/is.js'
import { factory } from '../../utils/factory.js'
import { createUtil } from './simplify/util.js'
import { noBignumber, noFraction } from '../../utils/noop.js'

const name = 'simplifyConstant'
const dependencies = [
  'typed',
  'config',
  'mathWithTransform',
  'matrix',
  '?fraction',
  '?bignumber',
  'AccessorNode',
  'ArrayNode',
  'ConstantNode',
  'FunctionNode',
  'IndexNode',
  'ObjectNode',
  'OperatorNode',
  'SymbolNode'
]

export const createSimplifyConstant = /* #__PURE__ */ factory(name, dependencies, ({
  typed,
  config,
  mathWithTransform,
  matrix,
  fraction,
  bignumber,
  AccessorNode,
  ArrayNode,
  ConstantNode,
  FunctionNode,
  IndexNode,
  ObjectNode,
  OperatorNode,
  SymbolNode
}) => {
  const { isCommutative, isAssociative, allChildren, createMakeNodeFunction } =
    createUtil({ FunctionNode, OperatorNode, SymbolNode })

  /**
   * simplifyConstant() takes a mathjs expression (either a Node representing
   * a parse tree or a string which it parses to produce a node), and replaces
   * any subexpression of it consisting entirely of constants with the computed
   * value of that subexpression.
   *
   * Syntax:
   *
   *     math.simplifyConstant(expr)
   *     math.simplifyConstant(expr, options)
   *
   * Examples:
   *
   *     math.simplifyConstant('x + 4*3/6')  // Node "x + 2"
   *     math.simplifyConstant('z cos(0)')   // Node "z 1"
   *     math.simplifyConstant('(5.2 + 1.08)t', {exactFractions: false})  // Node "6.28 t"
   *
   * See also:
   *
   *     simplify, simplifyCore, resolve, derivative
   *
   * @param {Node | string} node
   *     The expression to be simplified
   * @param {Object} options
   *     Simplification options, as per simplify()
   * @return {Node} Returns expression with constant subexpressions evaluated
   */
  const simplifyConstant = typed('simplifyConstant', {
    Node: node => _ensureNode(foldFraction(node, {})),

    'Node, Object': function (expr, options) {
      return _ensureNode(foldFraction(expr, options))
    }
  })

  function _removeFractions (thing) {
    if (isFraction(thing)) {
      return thing.valueOf()
    }
    if (thing instanceof Array) {
      return thing.map(_removeFractions)
    }
    if (isMatrix(thing)) {
      return matrix(_removeFractions(thing.valueOf()))
    }
    return thing
  }

  function _eval (fnname, args, options) {
    try {
      return mathWithTransform[fnname].apply(null, args)
    } catch (ignore) {
      // sometimes the implicit type conversion causes the evaluation to fail, so we'll try again after removing Fractions
      args = args.map(_removeFractions)
      return _toNumber(mathWithTransform[fnname].apply(null, args), options)
    }
  }

  const _toNode = typed({
    Fraction: _fractionToNode,
    number: function (n) {
      if (n < 0) {
        return unaryMinusNode(new ConstantNode(-n))
      }
      return new ConstantNode(n)
    },
    BigNumber: function (n) {
      if (n < 0) {
        return unaryMinusNode(new ConstantNode(-n))
      }
      return new ConstantNode(n) // old parameters: (n.toString(), 'number')
    },
    Complex: function (s) {
      throw new Error('Cannot convert Complex number to Node')
    },
    string: function (s) {
      return new ConstantNode(s)
    },
    Matrix: function (m) {
      return new ArrayNode(m.valueOf().map(e => _toNode(e)))
    }
  })

  function _ensureNode (thing) {
    if (isNode(thing)) {
      return thing
    }
    return _toNode(thing)
  }

  // convert a number to a fraction only if it can be expressed exactly,
  // and when both numerator and denominator are small enough
  function _exactFraction (n, options) {
    const exactFractions = (options && options.exactFractions !== false)
    if (exactFractions && isFinite(n) && fraction) {
      const f = fraction(n)
      const fractionsLimit = (options && typeof options.fractionsLimit === 'number')
        ? options.fractionsLimit
        : Infinity // no limit by default

      if (f.valueOf() === n && f.n < fractionsLimit && f.d < fractionsLimit) {
        return f
      }
    }
    return n
  }

  // Convert numbers to a preferred number type in preference order: Fraction, number, Complex
  // BigNumbers are left alone
  const _toNumber = typed({
    'string, Object': function (s, options) {
      if (config.number === 'BigNumber') {
        if (bignumber === undefined) {
          noBignumber()
        }
        return bignumber(s)
      } else if (config.number === 'Fraction') {
        if (fraction === undefined) {
          noFraction()
        }
        return fraction(s)
      } else {
        const n = parseFloat(s)
        return _exactFraction(n, options)
      }
    },

    'Fraction, Object': function (s, options) { return s }, // we don't need options here

    'BigNumber, Object': function (s, options) { return s }, // we don't need options here

    'number, Object': function (s, options) {
      return _exactFraction(s, options)
    },

    'Complex, Object': function (s, options) {
      if (s.im !== 0) {
        return s
      }
      return _exactFraction(s.re, options)
    },

    'Matrix, Object': function (s, options) {
      return matrix(_exactFraction(s.valueOf()))
    },

    'Array, Object': function (s, options) {
      return s.map(_exactFraction)
    }
  })

  function unaryMinusNode (n) {
    return new OperatorNode('-', 'unaryMinus', [n])
  }

  function _fractionToNode (f) {
    let n
    const vn = f.s * f.n
    if (vn < 0) {
      n = new OperatorNode('-', 'unaryMinus', [new ConstantNode(-vn)])
    } else {
      n = new ConstantNode(vn)
    }

    if (f.d === 1) {
      return n
    }
    return new OperatorNode('/', 'divide', [n, new ConstantNode(f.d)])
  }

  /* Handles constant indexing of ArrayNodes, matrices, and ObjectNodes */
  function _foldAccessor (obj, index, options) {
    if (!isIndexNode(index)) { // don't know what to do with that...
      return new AccessorNode(_ensureNode(obj), _ensureNode(index))
    }
    if (isArrayNode(obj) || isMatrix(obj)) {
      const remainingDims = Array.from(index.dimensions)
      /* We will resolve constant indices one at a time, looking
       * just in the first or second dimensions because (a) arrays
       * of more than two dimensions are likely rare, and (b) pulling
       * out the third or higher dimension would be pretty intricate.
       * The price is that we miss simplifying [..3d array][x,y,1]
       */
      while (remainingDims.length > 0) {
        if (isConstantNode(remainingDims[0]) &&
            typeof remainingDims[0].value !== 'string') {
          const first = _toNumber(remainingDims.shift().value, options)
          if (isArrayNode(obj)) {
            obj = obj.items[first - 1]
          } else { // matrix
            obj = obj.valueOf()[first - 1]
            if (obj instanceof Array) {
              obj = matrix(obj)
            }
          }
        } else if (remainingDims.length > 1 &&
                   isConstantNode(remainingDims[1]) &&
                   typeof remainingDims[1].value !== 'string') {
          const second = _toNumber(remainingDims[1].value, options)
          const tryItems = []
          const fromItems = isArrayNode(obj) ? obj.items : obj.valueOf()
          for (const item of fromItems) {
            if (isArrayNode(item)) {
              tryItems.push(item.items[second - 1])
            } else if (isMatrix(obj)) {
              tryItems.push(item[second - 1])
            } else {
              break
            }
          }
          if (tryItems.length === fromItems.length) {
            if (isArrayNode(obj)) {
              obj = new ArrayNode(tryItems)
            } else { // matrix
              obj = matrix(tryItems)
            }
            remainingDims.splice(1, 1)
          } else { // extracting slice along 2nd dimension failed, give up
            break
          }
        } else { // neither 1st or 2nd dimension is constant, give up
          break
        }
      }
      if (remainingDims.length === index.dimensions.length) {
        /* No successful constant indexing */
        return new AccessorNode(_ensureNode(obj), index)
      }
      if (remainingDims.length > 0) {
        /* Indexed some but not all dimensions */
        index = new IndexNode(remainingDims)
        return new AccessorNode(_ensureNode(obj), index)
      }
      /* All dimensions were constant, access completely resolved */
      return obj
    }
    if (isObjectNode(obj) &&
        index.dimensions.length === 1 &&
        isConstantNode(index.dimensions[0])) {
      const key = index.dimensions[0].value
      if (key in obj.properties) {
        return obj.properties[key]
      }
      return new ConstantNode() // undefined
    }
    /* Don't know how to index this sort of obj, at least not with this index */
    return new AccessorNode(_ensureNode(obj), index)
  }

  /*
   * Create a binary tree from a list of Fractions and Nodes.
   * Tries to fold Fractions by evaluating them until the first Node in the list is hit, so
   * `args` should be sorted to have the Fractions at the start (if the operator is commutative).
   * @param args - list of Fractions and Nodes
   * @param fn - evaluator for the binary operation evaluator that accepts two Fractions
   * @param makeNode - creates a binary OperatorNode/FunctionNode from a list of child Nodes
   * if args.length is 1, returns args[0]
   * @return - Either a Node representing a binary expression or Fraction
   */
  function foldOp (fn, args, makeNode, options) {
    const first = args.shift()

    // In the following reduction, sofar always has one of the three following
    // forms: [NODE], [CONSTANT], or [NODE, CONSTANT]
    const reduction = args.reduce((sofar, next) => {
      if (!isNode(next)) {
        const last = sofar.pop()

        if (isNode(last)) {
          return [last, next]
        }
        // Two constants in a row, try to fold them into one
        try {
          sofar.push(_eval(fn, [last, next], options))
          return sofar
        } catch (ignoreandcontinue) {
          sofar.push(last)
          // fall through to Node case
        }
      }

      // Encountered a Node, or failed folding --
      // collapse everything so far into a single tree:
      sofar.push(_ensureNode(sofar.pop()))
      const newtree = (sofar.length === 1) ? sofar[0] : makeNode(sofar)
      return [makeNode([newtree, _ensureNode(next)])]
    }, [first])

    if (reduction.length === 1) {
      return reduction[0]
    }
    // Might end up with a tree and a constant at the end:
    return makeNode([reduction[0], _toNode(reduction[1])])
  }

  // destroys the original node and returns a folded one
  function foldFraction (node, options) {
    switch (node.type) {
      case 'SymbolNode':
        return node
      case 'ConstantNode':
        switch (typeof node.value) {
          case 'number': return _toNumber(node.value, options)
          case 'string': return node.value
          default:
            if (!isNaN(node.value)) return _toNumber(node.value, options)
        }
        return node
      case 'FunctionNode':
        if (mathWithTransform[node.name] && mathWithTransform[node.name].rawArgs) {
          return node
        }
        {
          // Process operators as OperatorNode
          const operatorFunctions = ['add', 'multiply']
          if (operatorFunctions.indexOf(node.name) === -1) {
            const args = node.args.map(arg => foldFraction(arg, options))

            //console.log("TEST000", node)
            // If all args are numbers
            if (!args.some(isNode)) { // sqrt(8) or log(2)
              try {
                //console.log("Test00", node) // jcho
                //return _eval(node.name, args, options)
                const args2 = node.args.args.map(arg => foldFraction(arg, options))
                node.args = _eval(node.args[0].fn.toString(), args2, options)
                return node
              } catch (ignoreandcontinue) { }
            }

            // Size of a matrix does not depend on entries
            if (node.name === 'size' &&
                args.length === 1 &&
                isArrayNode(args[0])) {
              const sz = []
              let section = args[0]
              while (isArrayNode(section)) {
                sz.push(section.items.length)
                section = section.items[0]
              }
              return matrix(sz)
            }

            if (node.isTrigono || node.isArcTrigono) {
              const args0 = node.args[0]
              if (args0.isOperatorNode) {
                //console.log("TEST010", args0)
                if (args0.isBinary()) {
                  //console.log("TEST100", args0)
                  if (args0.fn === 'add' || args0.fn === 'subtract') {
                    // Polynomial
                  } else if (args0.fn === 'multiply') {  // sin((1/2)*x)
                    // console.log("TEST100", args0)
                    const args00 = args0.args[0]
                    const args01 = args0.args[1]
                    if ((args00.isOperatorNode && args00.fn === 'divide') && args01.isSymbolNode) {
                      if (args00.args[0].isConstantNode && args00.args[0].value === 1) {
                        const new_args00 = new OperatorNode('*', 'multiply', [args00.args[0], args01])
                        const new_args0 = new OperatorNode('/', 'divide', [new_args00, args00.args[1]])
                        return new FunctionNode(node.name, [new_args0])
                      }
                    } else if (args00.isOperatorNode && args00.isUnary() && args00.fn === 'unaryMinus') {
                      // console.log("TEST110", args00)
                    }
                  } else if (args0.fn === 'divide') {

                  }
                } else if (args0.isUnary() && args0.fn === 'unaryMinus') { // sin(-(1/2)*x)
                  //console.log("TEST333", args0)
                  const args1 = args0.args[0]
                  if (args1.fn === 'multiply') {  
                    // console.log("TEST200", args1)
                    const args00 = args1.args[0]
                    const args01 = args1.args[1]
                    if ((args00.isOperatorNode && args00.fn === 'divide') && args01.isSymbolNode) {
                      if (args00.args[0].isConstantNode && args00.args[0].value === 1) {
                        const new_args00 = new OperatorNode('*', 'multiply', [args00.args[0], args01])
                        const new_args1 = new OperatorNode('/', 'divide', [new_args00, args00.args[1]])
                        const new_arg = new OperatorNode('-', 'unaryMinus', [new_args1])
                        return new FunctionNode(node.name, [new_arg])
                      }
                    } else if (args00.isOperatorNode && args00.isUnary() && args00.fn === 'unaryMinus') {
                      //console.log("TEST210", args00)
                    }
                  }                  
                } else {
                  // console.log("Error - Display an expression in trigonometric function\n", args0)
                }
              }
            }
            
            if (node.name === 'abs' && options.calculateAbsolute) {
              // console.log("calculateAbsolute is on: ", node)
              const args0 = node.args[0]
              if (args0.isConstantNode) {
                return new ConstantNode(args0.value)
              } else if (args0.isOperatorNode && args0.isUnary() && args0.fn === 'unaryMinus') {
                const args00 = args0.args[0]
                if (args00.isConstantNode) {
                  return new ConstantNode(args00.value)
                }
              }
            }
            // Convert all args to nodes and construct a symbolic function call
            return new FunctionNode(node.name, args.map(_ensureNode))
          } else {
            // treat as operator
          }
        }
        /* falls through */
      case 'OperatorNode':
      {
        const fn = node.fn.toString()
        let args
        let res
        const makeNode = createMakeNodeFunction(node)

        //console.log("Debug - simplifyConstant:", node)

        if (isOperatorNode(node) && node.isUnary()) {
          args = [foldFraction(node.args[0], options)]
          if (!isNode(args[0])) {
            res = _eval(fn, args, options)
          } else {
            res = makeNode(args)
          }
        } else if (isAssociative(node, options.context)) {
          args = allChildren(node, options.context)
          args = args.map(arg => foldFraction(arg, options))

          if (fn === 'divide') { // 약분
            var coeff = []

            // Symbol (pi, e) 약분
            coeff = coeff.concat(coeffSymbolFromPoly(args[0]))
            coeff = coeff.concat(coeffSymbolFromPoly(args[1]))

            //console.log("Coefficients symbols: ", coeff)

            let existAllTerms = true
            for (let i = 0; i < coeff.length; i++) {
              if (coeff[i] !== 0) {
                existAllTerms = false
                break;
              }
            }

            if (existAllTerms) {
              //console.log("Before reduceFractionSymbol ", node.args[0], "\n", node.args[1])
              if (args[0].isSymbolNode && args[0].name === 'pi') {
                node.args[0] = new ConstantNode(1)
                //console.log("Test000 ", node)
              } else
                reduceFractionSymbol(node.args[0])

              if (args[1].isSymbolNode && args[1].name === 'pi')
                node.args[1] = new ConstantNode(1)
              else                
                reduceFractionSymbol(node.args[1])

              //console.log("After reduceFractionSymbol ", node.args[0], "\n", node.args[1])
              }

            // Coefficient 약분
            args = allChildren(node, options.context)
            args = args.map(arg => foldFraction(arg, options))
  
            coeff = []
            coeff = coeff.concat(coeffFromPoly(args[0]))
            coeff = coeff.concat(coeffFromPoly(args[1]))

            //console.log("Coefficients: ", coeff)

            const gcd = findGCD(coeff, coeff.length)

            //console.log("gcd = ", gcd)
            if (gcd > 1) {
              reduceFraction(args[0], gcd)
              reduceFraction(args[1], gcd)
            }
          }

          if (isCommutative(fn, options.context)) {
            // commutative binary operator
            const consts = []
            const vars = []

            for (let i = 0; i < args.length; i++) {
              if (!isNode(args[i])) {
                consts.push(args[i])
              } else {
                vars.push(args[i])
              }
            }

            if (consts.length > 1) {
              res = foldOp(fn, consts, makeNode, options)
              vars.unshift(res)
              res = foldOp(fn, vars, makeNode, options)
            } else {
              // we won't change the children order since it's not neccessary
              res = foldOp(fn, args, makeNode, options)
            }
          } else {
            // non-commutative binary operator
            res = foldOp(fn, args, makeNode, options)
          }
        } else {
          // non-associative binary operator
          if (fn === 'pow') {
            // console.log("simplifyConstant pow: args0", node.args[0], "\nargs1", node.args[1])
            const args0 = node.args[0]
            const args1 = node.args[1]
            
            if (args1.isOperatorNode) {
              if (args1.isBinary) {
                if ((args1.fn === 'add') || (args1.fn === 'subtract')) {
                  // Polynomial.
                  // Nothing to do.
                } else if (args1.fn === 'multiply') {  // sin((1/2)*x)
                  const args00 = args1.args[0]
                  const args01 = args1.args[1]
                  if ((args00.isOperatorNode && args00.fn === 'divide') && args01.isSymbolNode) {
                    if (args00.args[0].isConstantNode && args00.args[0].value === 1) {
                      const new_args00 = new OperatorNode('*', 'multiply', [args00.args[0], args01])
                      const new_args0 = new OperatorNode('/', 'divide', [new_args00, args00.args[1]])
                      return new OperatorNode('^', 'pow', [node.args[0], new_args0])
                    }
                  }
                } else if (args1.fn === 'divide') {
                  
                }
              } else if (args1.isUnary && args1.fn === 'unaryMinus') {

              } else {
                // console.log("Error - Display an expression in trigonometric function\n", args0)
              }
            } else if (args1.isConstantNode) {
              // console.log("simplifyConstant pow: args0", node.args[0], "\nargs1", node.args[1])
              if (args0.isFunctionNode && args0.fn.name === 'sqrt') {
                if (args1.value === 2) {
                  return args0.args[0]
                }
              }
            }
          }
          args = node.args.map(arg => foldFraction(arg, options))
          res = foldOp(fn, args, makeNode, options)
        }
        return res
      }
      case 'ParenthesisNode':
        // remove the uneccessary parenthesis
        return foldFraction(node.content, options)
      case 'AccessorNode':
        return _foldAccessor(
          foldFraction(node.object, options),
          foldFraction(node.index, options),
          options)
      case 'ArrayNode': {
        const foldItems = node.items.map(item => foldFraction(item, options))
        if (foldItems.some(isNode)) {
          return new ArrayNode(foldItems.map(_ensureNode))
        }
        /* All literals -- return a Matrix so we can operate on it */
        return matrix(foldItems)
      }
      case 'IndexNode': {
        return new IndexNode(
          node.dimensions.map(n => simplifyConstant(n, options)))
      }
      case 'ObjectNode': {
        const foldProps = {}
        for (const prop in node.properties) {
          foldProps[prop] = simplifyConstant(node.properties[prop], options)
        }
        return new ObjectNode(foldProps)
      }
      case 'AssignmentNode':
        /* falls through */
      case 'BlockNode':
        /* falls through */
      case 'FunctionAssignmentNode':
        /* falls through */
      case 'RangeNode':
        /* falls through */
      case 'ConditionalNode':
        /* falls through */
      default:
        throw new Error(`Unimplemented node type in simplifyConstant: ${node.type}`)
    }
  }

  return simplifyConstant


  function extractCoeff(node) { // 단항에 대한 상수 추출
    let result = 1
    //console.log("extractCoeff", node)

    if (node.isOperatorNode && node.isBinary()) {
      if (node.fn === 'multiply') {
        result *= extractCoeff(node.args[0])
        result *= extractCoeff(node.args[1])
      } 
    } else if (node.isOperatorNode && node.isUnary()) {
      result *= extractCoeff(node.args[0])
    } else if (node.isConstantNode) {
        return node.value
    } else if (node.isSymbolNode || node.isFunctionNode) {
        return 1;
    }
  
    return result
  }

  function coeffFromPoly(node) {
    let result = []
    //console.log("coeffFromPoly", node)

    if (node.isOperatorNode && node.isBinary()) {
      if (node.fn === 'add' || node.fn === 'subtract') {
        result = result.concat(coeffFromPoly(node.args[0]))
        result = result.concat(coeffFromPoly(node.args[1]))
      } else if (node.fn === 'multiply') {
        result.push(extractCoeff(node))
      } else if (node.fn === 'pow') {
        result.push(1)
      }
    } else if (node.isOperatorNode && node.isUnary()) {
      result.push(extractCoeff(node.args[0]))
    } else if (node.isFunctionNode || node.isSymbolNode) {
      result.push(1)
    } else if (node.isConstantNode) {
      result.push(node.value)
    } else if (node.isFraction) {
      result.push(node.n)
    } else {
      result.push(1)
    }

    //console.log("coeffFromPoly result: ", result)
    return result
  }

  function reduceFraction(node, gcd)
  {
    if (node.isOperatorNode && node.isBinary() && (node.fn === 'add' || node.fn === 'subtract')){
      reduceFraction(node.args[0], gcd)
      reduceFraction(node.args[1], gcd)
    } else if (node.isOperatorNode && node.isUnary) {
      reduceFraction(node.args[0], gcd)
    } else if (node.isOperatorNode && node.isBinary() && node.fn === 'multiply') {
      const args0 = node.args[0]
      if (args0.isConstantNode) {
        args0.value /= gcd
      } else if (args0.isOperatorNode && args0.isUnary) {
        if (args0.args[0].isConstantNode) {
          args0.args[0].value /= gcd
        }
      }  

      const args1 = node.args[1]
      if (args1.isConstantNode) {
        args1.value /= gcd
      } else if (args1.isOperatorNode && args1.isUnary) {
        if (args1.args[0].isConstantNode) {
          args1.args[0].value /= gcd
        }
      }  

    } else if (node.isConstantNode) {
      node.value /= gcd
    } else if (node.isFraction) {
      node.n /= gcd
    }
  }

  function extractCoeffSymbol(node) { // 단항에 대한 심볼 상수 (pi, e) 추출
    let result = 1
    //console.log("extractCoeffSymbol", node)

    if (node.isOperatorNode && node.isBinary()) {
      if (node.fn === 'multiply') {
        result *= extractCoeffSymbol(node.args[0])
        result *= extractCoeffSymbol(node.args[1])
      } 
    } else if (node.isOperatorNode && node.isUnary()) {
      result *= extractCoeffSymbol(node.args[0])
    } else if (node.isConstantNode) {
        return 1
    } else if (node.isSymbolNode && node.name === 'pi') {
        return 0;
    } else if (node.isFunctionNode) {
        return 1;
    }
  
    return result
  }

  function coeffSymbolFromPoly(node) {
    let result = []
    //console.log("coeffSymbolFromPoly", node)

    if (node.isOperatorNode && node.isBinary()) {
      if (node.fn === 'add' || node.fn === 'subtract') {
        result = result.concat(extractCoeffSymbol(node.args[0]))
        result = result.concat(extractCoeffSymbol(node.args[1]))
      } else if (node.fn === 'multiply') {
        result.push(extractCoeffSymbol(node))
      } else if (node.fn === 'pow') {
        result.push(1)
      }
    } else if (node.isOperatorNode && node.isUnary()) {
      result.push(extractCoeffSymbol(node.args[0]))
    } else if (node.isFunctionNode) {
      result.push(1)
    } else if (node.isSymbolNode && node.name === 'pi') {
      result.push(0)
    } else if (node.isConstantNode) {
      result.push(1)
    } else if (node.isFraction) {
      result.push(node.n)
    } else {
      result.push(1)
    }

    //console.log("coeffSymbolFromPoly result: ", result)
    return result
  }

  function reduceFractionSymbol(node)
  {
    //console.log("reduceFractionSymbol", node)

    if (node.isOperatorNode) {
      if (node.isBinary()) {
        if (node.fn === 'add' || node.fn === 'subtract') {
          reduceFractionSymbol(node.args[0])
          reduceFractionSymbol(node.args[1])
        } else if (node.fn === 'multiply') {
          const args0 = node.args[0]
          if (args0.isSymbolNode && args0.name === 'pi') {
            //console.log("Found args0 pi ", node)
            node.args[0] = new ConstantNode(1)
            //console.log("Changed args0 pi ", node)
          }
    
          const args1 = node.args[1]
          if (args1.isSymbolNode && args1.name === 'pi') {
            //console.log("Found args1 pi ", node)
            node.args[1] = new ConstantNode(1)
            //console.log("Changed args1 pi ", node)
          }
        } 
      } else if (node.isUnary()) {
        reduceFractionSymbol(node.args[0])
      }
    }
  }

  function gcd(a, b) {
    if (a == 0)
      return b;
    return gcd(b % a, a);
  }

  function findGCD(arr, n) {
    let result = arr[0]
    for (let i = 1; i < n; i++) {
      result = gcd(arr[i], result);

      if (result == 1) {
        return 1;
      }
    }
    return result;
  }
})
