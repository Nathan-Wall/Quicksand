/*# Quicksand
 *# Developed by Nathan Wall
 *# http://quicksand.joijs.com/
 *# 
 *# Design goals: Speed and accurate results are the top priorities for Quicksand.
 *# Readability and maintainability take a backseat to the speed of this library.
 *# This version of Quicksand is built for HTML only, but QuicksandParser fully
 *# supports Selectors Levels 3 (and the current draft of Selectors Level 4), including
 *# XML properties (such as namespaces). It wouldn't be hard to port Quicksand
 *# to XML or to use QuicksandParser as a foundation for building an XML selector.
 */

var Quicksand = (function() {
  
	'use strict';
	
	var undefined,
		
		fPush = Array.prototype.push,
		fUnshift = Array.prototype.unshift,
		fSplice = Array.prototype.splice,
		
		documentElement = document.documentElement,
		supportsHasAttribute = !!documentElement.hasAttribute,
		
		nextElId = 1,
		
		// Quicksand will produce an array of "fast track" regexes which can be used
		// to determine if there is a faster algorithm for finding a selection than
		// the full selector algorithm.
		fastTrack = [ ],
		fastTrackCache = { },
		
		supportsGetAttribute = !!documentElement.getAttribute,
		
		customPseudoClasses = { };
	 
	var		/* -- CONSTANTS --
		 * The numbering is based on the first draft of Selectors 4.
		 * Most of the numbering comes from the draft but is trivial in meaning (and subject to change).
		 * However, numbers in the 4xxxx range (40,000 to 49,999) represent
		 * Selector Level 4 additions and are therefore subject to change or removal.
		 * Numbers in the 9xxxx range (90,000 to 99,999) represent non-standard additions.
		 * Numbers in the 10xxxx range (100,000 to 199,999) are reserved for custom pseudo-classes.
		 * Negative numbers are references to highly experimental non-standard additions.
		 * An addition is considered highly-expiremental if there is good reason it may change
		 * or be removed in the future.
		 */
		
		// [ 14 Combinators ]
		DESCENDANT_COMBINATOR = 1401,
		CHILD_COMBINATOR = 1402,
		ADJACENT_SIBLING_COMBINATOR = 1403,
		GENERAL_SIBLING_COMBINATOR = 1404,
		REFERENCE_COMBINATOR = 41405, // CSS4
		
		// [ Pseudo-Classes ]
		
		// 4 Logical Combinations
		MATCHES_PSEUDOCLASS = 40401, // CSS4
		NOT_PSEUDOCLASS = 402,
		CONTAINS_PSEUDOCLASS = 90403, // non-standard
		
		// 7 Location Pseudo-classes
		ANY_LINK_PSEUDOCLASS = 40701, // CSS4
		LINK_PSEUDOCLASS = 702,
		VISITED_PSEUDOCLASS = 703,
		LOCAL_LINK_PSEUDOCLASS = 40704, // CSS4
		TARGET_PSEUDOCLASS = 705,
		SCOPE_PSEUDOCLASS = 40706, // CSS4
		
		// 8 User Action Pseudo-classes
		HOVER_PSEUDOCLASS = 801,
		ACTIVE_PSEUDOCLASS = 802,
		FOCUS_PSEUDOCLASS = 803,
		
		// 9 Time-dimensional Pseudo-classes
		CURRENT_PSEUDOCLASS = 40901, // CSS4
		PAST_PSEUDOCLASS = 40902, // CSS4
		FUTURE_PSEUDOCLASS = 40903, // CSS4
		
		// 10 Linguistic Pseudo-classes
		DIR_PSEUDOCLASS = 41001, // CSS4
		LANG_PSEUDOCLASS = 1002,
		
		// 11 UI States Pseudo-classes
		ENABLED_PSEUDOCLASS = 1101,
		DISABLED_PSEUDOCLASS = 1102,
		CHECKED_PSEUDOCLASS = 1103,
		UNCHECKED_PSEUDOCLASS = 91104, // non-standard
		INDETERMINATE_PSEUDOCLASS = 41105, // CSS4 (reserved in CSS3 but not implemented)
		DEFAULT_PSEUDOCLASS = 41106, // CSS4
		VALID_PSEUDOCLASS = 41107, // CSS4
		INVALID_PSEUDOCLASS = 41108, // CSS4
		IN_RANGE_PSEUDOCLASS = 41109, // CSS4
		OUT_OF_RANGE_PSEUDOCLASS = 41110, // CSS4
		REQUIRED_PSEUDOCLASS = 41111, // CSS4
		OPTIONAL_PSEUDOCLASS = 41112, // CSS4
		READ_ONLY_PSEUDOCLASS = 41113, // CSS4
		READ_WRITE_PSEUDOCLASS = 41114, // CSS4
		
		// 12 Tree-Structural Pseudo-classes
		ROOT_PSEUDOCLASS = 1201,
		NTH_CHILD_PSEUDOCLASS = 1202,
		NTH_LAST_CHILD_PSEUDOCLASS = 1203,
		NTH_OF_TYPE_PSEUDOCLASS = 1204,
		NTH_LAST_OF_TYPE_PSEUDOCLASS = 1205,
		NTH_MATCH_PSEUDOCLASS = 41206, // CSS4
		NTH_LAST_MATCH_PSEUDOCLASS = 41207, // CSS4
		NTH_PSEUDOCLASS = -1208, // non-standard (highly expiremental); Quicksand proposal replacement for CSS4 :nth-matches
		NTH_LAST_PSEUDOCLASS = -1209, // non-standard (higly experimental); Quicksand proposal; Quicksand proposal replacement for CSS4 :nth-last-matches
		FIRST_CHILD_PSEUDOCLASS = 1210,
		LAST_CHILD_PSEUDOCLASS = 1211,
		FIRST_OF_TYPE_PSEUDOCLASS = 1212,
		LAST_OF_TYPE_PSEUDOCLASS = 1213,
		ONLY_CHILD_PSEUDOCLASS = 1214,
		ONLY_OF_TYPE_PSEUDOCLASS = 1215,
		EMPTY_PSEUDOCLASS = 1216,
		
		// 13 Grid-Structural Pseudo-classes
		COLUMN_PSEUDOCLASS = 41301, // CSS4
		NTH_COLUMN_PSEUDOCLASS = 41302, // CSS4
		NTH_LAST_COLUMN_PSEUDOCLASS = 41303, // CSS4
		
		// [ 6 Attribute Selectors ]
		HAS_ATTRIBUTE_OPERATOR = 601,
		EQUALS_ATTRIBUTE_OPERATOR = 602,
		CONTAINS_WORD_ATTRIBUTE_OPERATOR = 603,
		STARTS_WITH_DASH_ATTRIBUTE_OPERATOR = 604,
		STARTS_WITH_ATTRIBUTE_OPERATOR = 605,
		ENDS_WITH_ATTRIBUTE_OPERATOR = 606,
		CONTAINS_ATTRIBUTE_OPERATOR = 607,
		DOESNT_EQUAL_ATTRIBUTE_OPERATOR = 90608, // non-standard
		DOESNT_CONTAIN_WORD_ATTRIBUTE_OPERATOR = 90609, // non-standard
		DOESNT_START_WITH_DASH_ATTRIBUTE_OPERATOR = 90610, // non-standard
		DOESNT_START_WITH_ATTRIBUTE_OPERATOR = 90611, // non-standard
		DOESNT_END_WITH_ATTRIBUTE_OPERATOR = 90612, // non-standard
		DOESNT_CONTAIN_ATTRIBUTE_OPERATOR = 90613, // non-standard
		
		// namespace constants
		NO_NAMESPACE = 401,
		DEFAULT_NAMESPACE = 402;
	
	var LOCAL_LINK_PARTIAL_ATTRIBUTE_OPERATOR = 100000,
		LOCAL_LINK_EXACT_ATTRIBUTE_OPERATOR = 100001;
	
	// include and setup QuicksandParser
	/*# QuicksandParser
 *# Developed by Nathan Wall
 *# http://quicksand.joijs.com/
 *# 
 *# Design goals: Create a readable, maintainable, CSS selector parser which
 *# conforms to Selectors Level 3 and Selectors Level 4, with the aim of producing
 *# selector objects which can be processed quickly to produce element results in
 *# the document. Unlike Quicksand, speed is not a top priority with QuicksandParser
 *# because the results can be cached.
 */

var QuicksandParser = (function() {
	
	/* Selectors Level 4 in this parser is based on:
	 * "W3C Working Draft 29 September 2011."
	 * http://www.w3.org/TR/selectors4/
	 */
	
	var undefined,
		
		/* css4Enabled is an expiremental feature. Due to the fact that CSS4 selectors
		 * are currently only in a first draft, this specification could change.
		 * Quicksand will adapt to the changes in the CSS4 specification as it is developed.
		 * To enable CSS4 features, use QuicksandParser.enableCss4();
		 */
		css4Enabled = false,
		
		/* extendedEnabled determines whether Quicksand's extended selector features are
		 * enabled.  If set to false, only standardized Selector Level 3 or 4 features will
		 * be available.
		 * To enable Quicksand's extended features, use QuicksandParser.enableExtended();
		 */
		extendedEnabled = false,
		
		/* experimentalEnabled can be used to enable extended selector features which are
		 * considered highly experimental. The difference between "experimental" and "extended"
		 * features is experimental features are considered likely to be open to change or
		 * removal in future versions of Quicksand, while extended features are considered
		 * more stable.
		 */
		experimentalEnabled = false,
		
		/* Allows the enabling of subject selectors ($) even if Css4Enabled is false.
		 * This is to account for the fact that a library may want to enable subject selectors without
		 * enabling broad CSS4 support and for the fact that subject selectors cannot be used with a prefix. 
		 * Note: If Css4Enabled is true, subject selectors will work even if subjectEnabled is false.
		 */
		subjectEnabled = false,
		
		/* Two subject modes are supported: ! and $
		 * In ! mode, the subject identifier (!) needs to be appended to the compound selector.
		 * In $ mode, the subject idetenfier ($) needs to be prepended to the compound selector.
		 */
		subjectMode = '!',
		
		/* Allows custom prefixes. Selector prefixes can be added with enableCss4, enableExtended,
		 * and enableExperimental. Note: The "-qs-" prefix is enabled by default but can be disabled
		 * with disableCss4, disableExtended, and disableExperimental.
		 */
		selectorPrefixes = [
			{
				prefix: '-qs-',
				css4: true,
				extended: true,
				experimental: true
			}
		],
		
		cacheEnabled = false,
		
		selectorCache = {
			selectorLists: { },
			itemSelectors: { }
		},
				
		reWhitespace = /\s/,
		
		subjectSet = false,
		
		nextCustomIdBase = 0;
	
	
	
	var parseSelector = (function() {
	
	var cache = selectorCache.itemSelectors;
	
	function parseSelector(selector, disableAutoUniversal, preTrimmed) {
		// disableAutoUniversal is used by :not to parse a selector without inserting an auto '*' type
		
		if(selector == '') throw 'QuicksandParser: Empty selector';
		
		var pSel = [ ], // The full parsed selector-list
			cpSel = [ ], // The current parsed selector
			pos = 0, xpos, res, firstPass, curCombinator = { type: DESCENDANT_COMBINATOR },
			itemEndGuess, cacheKey, item;
		
		pSel.original = selector;
		
		pSel.push(cpSel);
		
		// Advance past any leading whitespace in the selector.
		while(reWhitespace.test(selector.charAt(pos))) pos++;
		
		firstPass = true;
		subjectSet = false;
		while(pos < selector.length) {
			
			item = null;
			
			// Caching item selectors currently only works on descendant combinators
			if(cacheEnabled && curCombinator.type == DESCENDANT_COMBINATOR) {
				// Make an educated guess of what the compound selector is and see if it has been cached
				itemEndGuess = selector.indexOf(' ', pos);
				if(itemEndGuess == -1) cacheKey = selector.substring(pos);
				else cacheKey = selector.substring(pos, itemEndGuess);
				item = cache[cacheKey];
				if(item) {
					if(itemEndGuess == -1) pos = selector.length;
					else pos += itemEndGuess;
					cpSel.push(item);
				}
			}
			
			if(!item) {
				res = parseCompoundSelector(selector, pos, disableAutoUniversal);
				if(res) {
					item = {
						combinator: curCombinator,
						compoundSelector: res.cSel
					};
					if(cacheEnabled && pos == itemEndGuess) cache[cacheKey] = item;
					cpSel.push(item);
					pos = res.pos;
				} else if(!firstPass || !QuicksandParser.allowInitialCombinator) {
					throw 'QuicksandParser: Selector not understood at character ' + pos + ': ' + selector
						+ (firstPass ? '\nIf you are trying to start a selector with a combinator, allowInitialCombinator must be set to true' : '');
				}
			}
			firstPass = false;
			
			if(pos == selector.length) break;
			
			// Advance past any whitespace to see if the next character is a comma
			xpos = pos;
			while(reWhitespace.test(selector.charAt(xpos))) xpos++;
			if(selector.charAt(xpos) == ',') {
				pos = xpos;
				firstPass = true;
				subjectSet = false;
				cpSel = [ ];
				pSel.push(cpSel);
				pos++;
				// Advance past any leading whitespace in the selector.
				while(reWhitespace.test(selector.charAt(pos))) pos++;
			} else {
				
				res = parseCombinator(selector, pos);
				curCombinator = res.combSel;
				pos = res.pos;
				
				if(pos == selector.length && curCombinator) {
					if(QuicksandParser.allowTerminalCombinator) {
						cpSel.push({
							combinator: curCombinator,
							compoundSelector: {
								type: {
									namespace: DEFAULT_NAMESPACE,
									name: '*'
								}
							}
						});
					} else throw 'QuicksandParser: Selectors cannot end in a combinator unless allowTerminalCombinator is turned on: ' + selector;
				}
				
			}
			
		}
		
		return pSel;
		
	}
		
	return parseSelector;
	
})();
	var parseCombinator = (function() {
	
	function parseCombinator(selector, pos) {
		
		var combSel = { }, whitespaceFound = false, res;
		
		// Advance past whitespace
		while(reWhitespace.test(selector.charAt(pos))) {
			whitespaceFound = true;
			pos++;
		}
		
		if(pos >= selector.length) {
			// Don't mistake whitespace at the end of a selector for a descendant combinator.
			return {
				combSel: null,
				pos: pos
			};
		}
		
		switch(selector.charAt(pos)) {
			case '>': pos++; combSel.type = CHILD_COMBINATOR; break;
			case '+': pos++; combSel.type = ADJACENT_SIBLING_COMBINATOR; break;
			case '~': pos++; combSel.type = GENERAL_SIBLING_COMBINATOR; break;
			case '/': // CSS4
				if(!css4Enabled) throw 'QuicksandParser: Reference combinators are not allowed when CSS4 mode is disabled. To enable use ' + QuicksandParser.libName + '.enableCss4();';
				pos++;
				combSel.type = REFERENCE_COMBINATOR;
				res = getQualifiedName(selector, pos, true);
				pos = res.pos;
				if(res.namespace == DEFAULT_NAMESPACE) res.namespace = NO_NAMESPACE; // See [NOTE A] in loadAttribute
				combSel.attribute = {
					namespace: res.namespace,
					name: res.name
				};
				if(selector.charAt(pos) == '/') pos++;
				else throw 'QuicksandParser: Reference combinator not understood at character ' + pos + ' in selector: ' + selector;
				break;
			default:
				if(whitespaceFound) combSel.type = DESCENDANT_COMBINATOR;
				else throw 'QuicksandParser: Combinator expected but not found at position ' + pos + ' in selector: ' + selector;
				break;
		}
		
		// Advance past whitespace
		while(reWhitespace.test(selector.charAt(pos))) pos++;
		
		return {
			combSel: combSel,
			pos: pos
		};
		
	}
	
	return parseCombinator;
	
})();
	var parseCompoundSelector = (function() {
	
	function parseCompoundSelector(selector, pos, disableAutoUniversal) {
		
		if(pos >= selector.length) return null;
		
		var cSel, // The compound selector object
			c, res, initPos = pos, isSubject,
			checkFilterLast = false; // make sure the filter (:nth or :nth-last) is the last part of the compound selector
			
		cSel = { };
		
		if(selector.charAt(pos) == '$') {
			if(subjectMode == '$') {
				if(!css4Enabled && !subjectEnabled) throw 'QuicksandParser: Subject selectors ($) cannot be used in CSS3 mode. To enable use ' + QuicksandParser.libName + '.enableCss4() or ' + QuicksandParser.libName + '.enableSubject().';
				if(subjectSet) throw 'QuicksandParser: A selector cannot have two subjects (character ' + pos + '): ' + selector;
				// This is the subject of the selector
				cSel.subject = true;
				pos++;
				subjectSet = true;
				isSubject = true;
			} else throw 'QuicksandParser: Symbol not expected ($). If you are trying to use a subject selector, set subject mode to "$" using ' + QuicksandParser.libName + '.enableSubject("$").';
		}
		
		// Get the type (tag) selector
		res = getQualifiedName(selector, pos, true);
		cSel.type = {
			namespace: res.namespace,
			name: res.name
		};
		if(!cSel.type.name && !disableAutoUniversal) cSel.type.name = '*';
		pos = res.pos;
		
		while(c = selector.charAt(pos)) {
			
			if(cSel.filter) {
				if(checkFilterLast) throw 'QuicksandParser: The pseudo-classes :nth and :nth-last must be the last part of a compound selector.';
				else checkFilterLast = true;
			}
			
			switch(c) {
				case '#': pos = loadId(cSel, selector, pos + 1); break;
				case ':': pos = loadPseudoClass(cSel, selector, pos + 1); break;
				case '.': pos = loadClass(cSel, selector, pos + 1); break;
				case '[': pos = loadAttribute(cSel, selector, pos + 1); break;
				default:
					// Return null if no selectors were found
					if(pos == initPos) return null;
					else if(isSubject && pos - 1 == initPos) {
						// The only thing in this compount selector was the subject selector.
						throw 'QuicksandParser: The subject identifier cannot be alone (character ' + pos + '): ' + selector;
					} else {
						if(c == '!') {
							if(subjectMode == '!') {
								if(!css4Enabled && !subjectEnabled) throw 'QuicksandParser: Subject selectors (!) cannot be used in CSS3 mode. To enable use ' + QuicksandParser.libName + '.enableCss4() or ' + QuicksandParser.libName + '.enableSubject().';
								if(subjectSet) throw 'QuicksandParser: A selector cannot have two subjects (character ' + pos + '): ' + selector;
								cSel.subject = true;
								pos++;
								subjectSet = true;
								isSubject = true;
							} else throw 'QuicksandParser: Symbol not expected (!). If you are trying to use a subject selector, set subject mode to "!" using ' + QuicksandParser.libName + '.enableSubject("!").';
						}
						return {
							cSel: cSel,
							pos: pos
						};
					}
			}
			
		}
		
		if(checkFilterLast) throw 'QuicksandParser: The pseudo-classes :nth and :nth-last must be the last part of a compound selector.';
		
		// Return null if no selectors were found
		if(pos == initPos) return null;
		else if(isSubject && pos - 1 == initPos) {
			// The only thing in this compount selector was the $ symbol.
			throw 'QuicksandParser: The subject identifier ($) must be prepended to a compound selector (character ' + pos + '): ' + selector;
		} else return {
			cSel: cSel,
			pos: pos
		};
		
	}
		
	return parseCompoundSelector;
	
})();
	var getQualifiedName = (function() {
	
	function getQualifiedName(selector, pos, allowWildcard) {
		/* There are two types of blank namespaces.
		 * foo 		- will have a namespace of DEFAULT_NAMESPACE
		 * |foo		- will have a namespace of NO_NAMESPACE
		 */
		
		var res, namespace, name;
		
		res = getIdentifier(selector, pos);
		name = res.identifier;
		pos = res.pos;
		
		if(!name) {
			if(allowWildcard && selector.charAt(pos) == '*') {
				name = '*';
				pos++;
			} else name = undefined;
		}
		
		if(selector.charAt(pos) == '|') {
			// namespace
			
			res = getIdentifier(selector, pos + 1);
			
			if(res.pos != pos + 1) {
				// Only accept an identifier. This helps with cases like "div[attr|=value]" because otherwise "attr" is seen
				// as a namespace with no name following the "|". But in this case "|=" is an operator.
				namespace = name;
				name = res.identifier;
				pos = res.pos;
				
				if(!name) {
					if(allowWildcard && selector.charAt(pos) == '*') {
						name = '*';
						pos++;
					} else name = undefined;
				}
				
				if(!namespace) namespace = NO_NAMESPACE;
			}
			
		} else namespace = DEFAULT_NAMESPACE;
		
		return {
			namespace: namespace,
			name: name,
			pos: pos
		};
		
	}
	
	return getQualifiedName;
	
})();
	var getIdentifier = (function() {
	
	var reNextNonWord = /[^\w\-]/,
		reNumber = /[0-9]/;
	
	function getIdentifier(selector, pos) {
		
		var initPos = pos, c, nextNW, res, realPosDiff = 0;
		
		c = selector.charAt(pos);
		if(reNumber.test(c)) {
			// identifier cannot start with a number
			return {
				identifier: null,
				pos: pos
			};
		}
		
		if(c == '-') {
			c = selector.charAt(pos + 1);
			if(c == '-' || reNumber.test(c)) {
				// identifier cannot start with two hyphens or a hyphen and a number
				return {
					identifier: null,
					pos: pos
				};
			}
		}
		
		while(pos < selector.length) {
			nextNW = selector.substring(pos).search(reNextNonWord);
			if(~nextNW) pos += nextNW;
			else {
				// All remaining characters are word characters, so return the rest of the string
				pos = selector.length;
				return {
					identifier: selector.substring(initPos),
					pos: pos
				};
			}
			c = selector.charAt(pos);
			if(c == '\\') {
				res = replaceEscapedChars(selector, pos);
				pos = res.pos;
				selector = res.selector;
				realPosDiff += res.realPos - pos;
			} else if(c >= '\u00a0') {
				// All characters above U+00A0 can be a part of an identifier
				pos++;
			} else {
				// The end of the identifier has been reached
				break;
			}
		}
		
		return {
			identifier: selector.substring(initPos, pos),
			pos: pos + realPosDiff
		};
		
	}
	
	return getIdentifier;
	
})();
	var loadId = (function() {
	
	function loadId(cSel, selector, pos) {
		
		var res, id;
		
		res = getIdentifier(selector, pos);
		id = res.identifier;
		pos = res.pos;
		
		if(!id) throw 'QuicksandParser: Id selector empty in: ' + selector;
		
		cSel.id = id;
				
		return pos;
		
	}
	
	return loadId;
	
})();
	var pseudoClassTypes,
	requireArgument;

var loadPseudoClass = (function() {
	
	pseudoClassTypes = {
		
		'matches': MATCHES_PSEUDOCLASS,
		'not': NOT_PSEUDOCLASS,
		'contains': CONTAINS_PSEUDOCLASS,
		
		'any-link': ANY_LINK_PSEUDOCLASS,
		'link': LINK_PSEUDOCLASS,
		'visited': VISITED_PSEUDOCLASS,
		'local-link': LOCAL_LINK_PSEUDOCLASS,
		'target': TARGET_PSEUDOCLASS,
		'scope': SCOPE_PSEUDOCLASS,
		
		'hover': HOVER_PSEUDOCLASS,
		'active': ACTIVE_PSEUDOCLASS,
		'focus': FOCUS_PSEUDOCLASS,
		
		'current': CURRENT_PSEUDOCLASS,
		'past': PAST_PSEUDOCLASS,
		'future': FUTURE_PSEUDOCLASS,
		
		'dir': DIR_PSEUDOCLASS,
		'lang': LANG_PSEUDOCLASS,
		
		'enabled': ENABLED_PSEUDOCLASS,
		'disabled': DISABLED_PSEUDOCLASS,
		'checked': CHECKED_PSEUDOCLASS,
		'unchecked': UNCHECKED_PSEUDOCLASS,
		'indeterminate': INDETERMINATE_PSEUDOCLASS,
		'default': DEFAULT_PSEUDOCLASS,
		'valid': VALID_PSEUDOCLASS,
		'invalid': INVALID_PSEUDOCLASS,
		'in-range': IN_RANGE_PSEUDOCLASS,
		'out-of-range': OUT_OF_RANGE_PSEUDOCLASS,
		'required': REQUIRED_PSEUDOCLASS,
		'optional': OPTIONAL_PSEUDOCLASS,
		'read-only': READ_ONLY_PSEUDOCLASS,
		'read-write': READ_WRITE_PSEUDOCLASS,
		
		'root': ROOT_PSEUDOCLASS,
		'nth-child': NTH_CHILD_PSEUDOCLASS,
		'nth-last-child': NTH_LAST_CHILD_PSEUDOCLASS,
		'nth-of-type': NTH_OF_TYPE_PSEUDOCLASS,
		'nth-last-of-type': NTH_LAST_OF_TYPE_PSEUDOCLASS,
		'nth-match': NTH_MATCH_PSEUDOCLASS,
		'nth-last-match': NTH_LAST_MATCH_PSEUDOCLASS,
		'nth': NTH_PSEUDOCLASS,
		'nth-last': NTH_LAST_PSEUDOCLASS,
		'first-child': FIRST_CHILD_PSEUDOCLASS,
		'last-child': LAST_CHILD_PSEUDOCLASS,
		'first-of-type': FIRST_OF_TYPE_PSEUDOCLASS,
		'last-of-type': LAST_OF_TYPE_PSEUDOCLASS,
		'only-child': ONLY_CHILD_PSEUDOCLASS,
		'only-of-type': ONLY_OF_TYPE_PSEUDOCLASS,
		'empty': EMPTY_PSEUDOCLASS,
		
		'column': COLUMN_PSEUDOCLASS,
		'nth-column': NTH_COLUMN_PSEUDOCLASS,
		'nth-last-column': NTH_LAST_COLUMN_PSEUDOCLASS
		
	};
	
	// The following pseudo-classes require arguments
	// False doesn't explicitly need to be set for pseudo-classes which don't require arguments,
	// but I'm doing it for some of them here as a reminder that I didn't just forget them.
	// (To remind myself that they can (or at least sound like they could) be argumentless)
	// TODO: When the next draft of Selectors Level 4 comes out some of these might need to be readdressed.
	requireArgument = {
		'nth-child': true,
		'nth-last-child': true,
		'nth-of-type': true,
		'nth-last-of-type': true,
		'nth-match': true,
		'nth-last-match': true,
		'nth': true,
		'nth-last': true,
		'column': false, // I'm unsure about this one, so I'm just setting it to false for now. Can revisit later and make true if it needs to be.
		'nth-column': true,
		'nth-last-column': true,
		'not': true,
		'matches': true,
		'current': false, // current, past, and future seem like they can be argumentless from the spec
		'past': false,
		'future': false,
		'dir': false,
		'lang': true,
		'contains': true
	};
	
	var reANpB = /^([0-9]+)?n([\+\-][0-9]+)?$|^[\-]?[0-9]+$/, // an+b
		
		/* This may need to be changed as Selectors 4 evolves.
		 * The current draft seems to have " of " separating the arguments, while
		 * I have seen some places with ", " separating the arguments.
		 */
		reNthMatchesSplitter = /\s+of\s+/,
		
		reIsInteger = /^[0-9]+$/,
		reEndWhitespace = /\s+$/,
		reCommaSeparator = /\s*\,\s*/;
	
	function loadPseudoClass(cSel, selector, pos) {
		// returns the position of the end of the pseudo-class
		
		var c, initPos = pos,
			pseudoClassInfo, pseudoClass, pseudoClassName, cPseudoClass,
			res, openParens = 0, argument, matches, realPosDiff = 0, stringOpen,
			_css4Enabled = css4Enabled,
			_extendedEnabled = extendedEnabled,
			_experimentalEnabled = experimentalEnabled;
		
		if(!cSel.pseudoClasses) cSel.pseudoClasses = [ ];
		
		res = getIdentifier(selector, pos);
		pseudoClassName = res.identifier;
		pseudoClass = pseudoClassTypes[ pseudoClassName ];
		if(!pseudoClass) {
			pseudoClassInfo = evaluatePrefix(pseudoClassName);
			if(pseudoClassInfo) {
				pseudoClassName = pseudoClassInfo.identifier;
				pseudoClass = pseudoClassTypes[ pseudoClassName ];
				if(pseudoClassInfo.css4) _css4Enabled = true;
				if(pseudoClassInfo.extended) _extendedEnabled = true;
				if(pseudoClassInfo.experimental) _experimentalEnabled = true;
			}
		}
		pos = res.pos;
		
		// cPseudoClass allows checking custom pseudo-class properties as well
		// (whether they should be considered extended, css4, or experimental).
		cPseudoClass = pseudoClass;
		if(cPseudoClass > 100000) cPseudoClass -= 100000;
		
		if(!pseudoClass) throw 'QuicksandParser: Pseudo-class not recognized: ' + selector.substring(initPos, pos);
		if(!_css4Enabled && cPseudoClass >= 40000 && cPseudoClass < 50000) throw 'QuicksandParser: Pseudo-class not supported in CSS3 mode. Use ' + QuicksandParser.libName + '.enableCss4().';
		if(!_extendedEnabled && cPseudoClass >= 90000 && cPseudoClass < 100000) throw 'QuicksandParser: Pseudo-class not supported in standard mode. Use ' + QuicksandParser.libName + '.enableExtended().';
		if(!_experimentalEnabled && pseudoClass < 0) throw 'QuicksandParser: Pseudo-class not supported in standard mode. Use ' + QuicksandParser.libName + '.enableExperimental().';
		
		c = selector.charAt(pos);
		if(c == '(') {
			
			// load argument
			pos++;
			while(reWhitespace.test(selector.charAt(pos))) pos++; // Advance past any leading whitespace
			initPos = pos;
			openParens = 1;
			stringOpen = false;
			while(c = selector.charAt(pos)) {
				if(!stringOpen && c == ')') {
					openParens--;
					if(openParens == 0) {
						pos++;
						break;
					}
				} else if(!stringOpen && c == '(') openParens++;
				else if(c == '\\')  {
					res = replaceEscapedChars(selector, pos);
					selector = res.selector;
					pos = res.pos - 1;
					realPosDiff += res.realPos - pos;
				} else if(c == '"' || c == "'") {
					stringOpen = !stringOpen;
				}
				pos++;
			}
			argument = selector.substring(initPos, pos - 1);
			// Trim any trailing whitespace from the argument
			if(reEndWhitespace.test(argument)) argument = argument.substring(0, argument.search(reEndWhitespace));
			if(argument == '') throw 'Quicksand Parser: Pseudo-class argument cannot be empty.';
			
			switch(pseudoClass) {
				case NTH_CHILD_PSEUDOCLASS:
				case NTH_LAST_CHILD_PSEUDOCLASS:
				case NTH_OF_TYPE_PSEUDOCLASS:
				case NTH_LAST_OF_TYPE_PSEUDOCLASS:
				case NTH_COLUMN_PSEUDOCLASS:
				case NTH_LAST_COLUMN_PSEUDOCLASS:
					// Argument should be in the form an+b or "even" or "odd"
					matches = matchANpB(argument);
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						a: matches.a,
						b: matches.b
					});
					break;
				case NTH_PSEUDOCLASS:
				case NTH_LAST_PSEUDOCLASS:
					// Argument should be in the form an+b or "even" or "odd"
					if(cSel.filter) throw 'QuicksandParser: A filter has already been defined for this compound selector: ' + pseudoClass;
					matches = matchANpB(argument);
					cSel.filter = {
						type: pseudoClass,
						a: matches.a,
						b: matches.b
					};
					break;
				case NTH_MATCH_PSEUDOCLASS:
				case NTH_LAST_MATCH_PSEUDOCLASS:
					argument = argument.split(reNthMatchesSplitter);
					if(argument.length != 2) throw 'QuicksandParser: Argument not understood: ' + argument.join(' | ');
					matches = matchANpB(argument[0]);
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						a: matches.a,
						b: matches.b,
						selector: parseSelector(argument[1])
					});
					break;
				case CURRENT_PSEUDOCLASS:
					// It sounds like, from the draft, :current can be argumentless or have a selector list argument.
				case PAST_PSEUDOCLASS:
				case FUTURE_PSEUDOCLASS:
					// The first draft mentions nothing of :past and :future having an argument, but it seems that they would from their similarity to :current
					// TODO: When next draft comes out, check to see if there's an update to this.
				case COLUMN_PSEUDOCLASS:
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						selector: parseSelector(argument)
					});
					break;
				case MATCHES_PSEUDOCLASS:
				case NOT_PSEUDOCLASS:
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						selector: parseSelector(argument, true) // The true argument disables auto-universal type insertion
					});
					break;
				case CONTAINS_PSEUDOCLASS: // non-standard
					// Argument must be a "keyword" or quoted string as per Selectors Candidate Recommendation 13 November 2001
					// http://www.w3.org/TR/2001/CR-css3-selectors-20011113/#content-selectors
					// Since it is unclear what is meant by "keyword", Quicksand allows identifiers.
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						content: parseStringArgument(argument)
					});
					break;
				case DIR_PSEUDOCLASS:
					// ltr and rtl are the only defined arguments, but the draft says any identifier is "acceptable" and others may be accepted and implemented in the future
					if(!isIdentifier(argument)) throw 'QuicksandParser: Argument for :dir pseudo-class must be a valid identifier.';
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						direction: argument
					});
					break;
				case LANG_PSEUDOCLASS:
					// Check to make sure the argument is a valid identifier
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						languages: splitLanguages(argument)
					});
					break;
				case LOCAL_LINK_PSEUDOCLASS:
					// The argument must be an integer
					if(!reIsInteger.test(argument)) throw 'QuicksandParser: Argument for :local-link pseudo-class must be a single integer.';
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						pathLevels: argument * 1
					});
					break;
				default:
					// Custom pseudo-class arguments aren't handled here, so don't throw an error if the pseudo-class is custom.
					if(pseudoClass < 100000) throw 'QuicksandParser: Argument not expected for pseudo-class ' + pseudoClassName + ': ' + argument;
					cSel.pseudoClasses.push({
						pseudoClass: pseudoClass,
						argument: argument
					});
					break;
			}
			
		} else {
			if(requireArgument[ pseudoClassName ]) throw 'QuicksandParser: Pseudo-class :' + pseudoClassName + ' requires an argument.';
			cSel.pseudoClasses.push({
				pseudoClass: pseudoClass
			});
		}
		
		return pos + realPosDiff;
		
	}
	
	function matchANpB(argument) {
		var matches, a, b;
		argument = argument.toLowerCase();
		if(argument == 'even') { a = 2; b = 0; }
		else if(argument == 'odd') { a = 2; b = 1; }
		else {
			matches = reANpB.exec(argument);
			if(matches) {
				if(~matches[0].indexOf('n')) {
					if(matches[1]) a = matches[1] * 1;
					else a = 1;
					if(matches[2]) b = matches[2] * 1;
					else b = 0;
				} else {
					a = 0;
					b = matches[0] * 1;
				}
			} else throw('QuicksandParser: Pseudo-class argument not understood: ' + argument);
		}
		return {
			a: a,
			b: b
		};
	}
	
	function isIdentifier(test) {
		res = getIdentifier(test, 0);
		return test == res.identifier;
	}
	
	function parseStringArgument(argument) {
		// Accepts a single identifier or a string enclosed in quotes as the arugment
		var c = argument.charAt(0), c2, res, identifier, pos;
		if(c == '"' || c == "'") {
			c2 = argument.charAt(argument.length - 1);
			if(c2 != c) throw 'QuicksandParser: Argument not understood: ' + argument;
			return argument.substring(1, argument.length - 1);
		} else {
			res = getIdentifier(argument, 0);
			identifier = res.identifier;
			pos = res.pos;
			if(pos < argument.length) throw 'QuicksandParser: Argument not understood: ' + argument;
			return identifier;
		}
	}
	
	function splitLanguages(argument) {
		// Note: Although the first Working Draft of Selectors 4 doesn't state that :lang should accept multiple
		// languages, the Editor's Draft (http://dev.w3.org/csswg/selectors4/#lang-pseudo) does.
		var langs = argument.split(reCommaSeparator), lang;
		for(var i = 0; i < langs.length; i++) {
			lang = trim(langs[i]);
			if(lang.substring(0, 2) == '*-') {
				if(!isIdentifier(lang.substring(2))) throw 'QuicksandParser: Arguments for :lang pseudo-class must be valid identifiers or begin with "*-".';
			} else if(!isIdentifier(lang)) throw 'QuicksandParser: Arguments for :lang pseudo-class must be valid identifiers or begin with "*-".';
			if(~lang.indexOf('--')) throw 'QuicksandParser: Argument for :lang should not contain two dashes.';
			lang[i] = lang;
		}
		return langs;
	}
		
	function evaluatePrefix(identifier) {
		var pObj, prefix;
		for(var i = 0; i < selectorPrefixes.length; i++) {
			pObj = selectorPrefixes[i];
			prefix = pObj.prefix;
			if(identifier.substring(0, prefix.length) == prefix) {
				return {
					identifier: identifier.substring(prefix.length),
					css4: pObj.css4,
					extended: pObj.extended,
					experimental: pObj.experimental
				};
			}
		}
		return false;
	}
	
	return loadPseudoClass;
	
})();
	function loadClass(cSel, selector, pos) {
	// returns the position of the end of the class
	
	var res = getIdentifier(selector, pos),
		className = res.identifier,
		pos = res.pos;
	
	if(!cSel.classes) cSel.classes = [ ];
	cSel.classes.push(className);
	
	return pos;
	
}

	var loadAttribute = (function() {
	
	var operatorMap = {
		'=': EQUALS_ATTRIBUTE_OPERATOR,
		'~=': CONTAINS_WORD_ATTRIBUTE_OPERATOR,
		'|=': STARTS_WITH_DASH_ATTRIBUTE_OPERATOR,
		'^=': STARTS_WITH_ATTRIBUTE_OPERATOR,
		'$=': ENDS_WITH_ATTRIBUTE_OPERATOR,
		'*=': CONTAINS_ATTRIBUTE_OPERATOR,
		'!=': DOESNT_EQUAL_ATTRIBUTE_OPERATOR,
		'!~=': DOESNT_CONTAIN_WORD_ATTRIBUTE_OPERATOR,
		'!|=': DOESNT_START_WITH_DASH_ATTRIBUTE_OPERATOR,
		'!^=': DOESNT_START_WITH_ATTRIBUTE_OPERATOR,
		'!$=': DOESNT_END_WITH_ATTRIBUTE_OPERATOR,
		'!*=': DOESNT_CONTAIN_ATTRIBUTE_OPERATOR
	};
	
	function loadAttribute(cSel, selector, pos) {
		
		var res, namespace, name, value, initPos = pos, operator, c;
		
		res = getQualifiedName(selector, pos, true);
		namespace = res.namespace;
		name = res.name;
		pos = res.pos;
		
		// [NOTE A]: According to section 6.4 of the first draft,
		// if no namespace is specified, do not use a default for attributes. The only attributes that should
		// match are those with no namespace. i.e. [foo=bar] is the same as [|foo=bar]
		// The following line makes this explicit.
		if(namespace == DEFAULT_NAMESPACE) namespace = NO_NAMESPACE;
		
		if(!name) throw 'QuicksandParser: Attribute selector not understood at character ' + pos + ' for selector: ' + selector;
		
		c = selector.charAt(pos);
		pos++;
		if(c == ']') {
			// no value / end of attribute selector
			addAttribute(cSel, namespace, name, HAS_ATTRIBUTE_OPERATOR);
			return pos;
		}
		
		// Load operator
		operator = c;
		if(c != '=') {
			while(c = selector.charAt(pos)) {
				operator += c;
				pos++;
				if(c == '=') break;
			}
		}
		operator = operatorMap[operator];
		if(!operator) throw 'QuicksandParser: Attribute selector not understood for selector: ' + selector;
		
		if(!extendedEnabled && operator > 90000) throw 'QuicksandParser: Extended features currently disabled for selector: ' + selector + '\nUse ' + QuicksandParser.libName + '.enableExtended();';
		
		res = getValue(selector, pos);
		value = res.value;
		pos = res.pos;
		
		if(selector.charAt(pos) == ']') {
			addAttribute(cSel, namespace, name, operator, value);
			pos++;
		} else if(reWhitespace.test(selector.charAt(pos))) {
			pos++;
			while(c = selector.charAt(pos)) {
				if(!reWhitespace.test(c)) break;
				pos++;
			}
			if(c == 'i' && selector.charAt(pos + 1) == ']') {
				addAttribute(cSel, namespace, name, operator, value, true);
				pos += 2;
			} else throw 'QuicksandParser: Attribute selector not understood for selector: ' + selector;
		} else throw 'QuicksandParser: Attribute selector not understood for selector: ' + selector;
		
		return pos;
		
	}
	
	function addAttribute(cSel, namespace, name, operator, value, caseInsensitive) {
		var attrSel = {
			namespace: namespace,
			name: name,
			operator: operator
		};
		if(!cSel.attributes) cSel.attributes = [ ];
		if(value) attrSel.value = value;
		if(caseInsensitive) attrSel.caseInsensitive = true;
		cSel.attributes.push(attrSel);
	}
	
	function getValue(selector, pos) {
		
		var c, startQuote, startQuotePos, res;
		
		c = selector.charAt(pos);
		
		if(c == '"' || c == "'") {
			startQuote = c;
			pos++;
			startQuotePos = pos;
			while(c = selector.charAt(pos)) {
				if(c == startQuote) break;
				if(c == '\\') {
					// increase an extra space to skip escaped quotes
					pos++;
					if(!selector.charAt(pos)) break;
				}
				pos++;
			}
			if(!c) {
				return {
					pos: startQuotePos - 1,
					value: ''
				};
			}
			pos++; // Advance past the closing quote
			return {
				value: parseString(selector.substring(startQuotePos, pos - 1)),
				pos: pos
			};
		} else {
			res = getIdentifier(selector, pos);
			return {
				value: res.identifier,
				pos: res.pos
			};
		}
		
	}
	
	function parseString(s) {
		// Remove escaped characters from a string
		var slashPos = s.indexOf('\\'), res, pos;
		while(slashPos != -1) {
			res = replaceEscapedChars(s, slashPos);
			s = res.selector;
			pos = res.pos;
			slashPos = s.indexOf('\\', pos);
		}
		return s;
	}
	
	return loadAttribute;
	
})();
	var replaceEscapedChars = (function() {
	
	var reHexNum = /[0-9a-fA-F]/;
	
	function replaceEscapedChars(selector, pos) {
		
		var hexCount = 0, initPos = pos, c, hexNum,
			
			// realPos is for keeping up with the position in the original string,
			// while pos keeps up with the position as the string changes
			realPos;
		
		pos++; // skip backslash
		c = selector.charAt(pos);
		
		if(reHexNum.test(c)) {
			// An escaped hexidecimal number
			
			do {
				hexCount++;
				pos++;
			} while(reHexNum.test(selector.charAt(pos)) && hexCount < 6);
			realPos = pos; // realPos is the position in the original selector
			
			hexNum = parseInt(selector.substring(initPos + 1, pos), 16);
			if(hexNum == 0) throw 'Quicksand: Hexidecimal value "0" not allowed after an escape character.';
			if(hexNum > 0x10ffff) hexNum = 0xfffd; // replace numbers too large with "replacement character"
			c = hexToChar(hexNum);
			selector = selector.substring(0, initPos) + c + selector.substring(pos);
			// adjust pos to account for the change in the selector
			// c.length is used instead of 1 because some unicode "characters" may have length of 2
			// https://developer.mozilla.org/en/JavaScript/Reference/Global_Objects/String/fromCharCode
			pos = initPos + c.length;
			
			c = selector.charAt(pos);
			if(reWhitespace.test(c)) {
				// If the hex code was terminated by a whitespace character, then remove it.
				if(c == '\r' && selector.charAt(pos + 1) == '\n') {
					
					// Remove both \r and \n characters if they both follow a hex code
					selector = selector.substring(0, pos) + selector.substring(pos + 2);
					
					// pos is already at the next character after the removed space.
					// No backup or forward operation is needed.
					
					// Increase realPos to account for the extra character
					realPos++;
					
				} else {
					selector = selector.substring(0, pos) + selector.substring(pos + 1);
					// pos is already at the next character after the removed space.
					// No backup or forward operation is needed.
				}
				// Increase realPos to account for the character
				realPos++;
			}
			
		} else if(c == '\n' || c == '\r') {
			/* The specification states that outside of strings a backslash followed by a new line
			 * stands for itself. So skip only the backslash, don't replace anything, and continue
			 * processing at the new line.  In other words, this codepath is left intentionally blank
			 * because nothing should happen in this case.
			 * http://www.w3.org/TR/CSS21/syndata.html#characters
			 * 
			 * TODO: A backslash inside a string followed by a new line should ignore both the backslash
			 * and the new line.  At this time, string processing hasn't been set up, but this issue may
			 * need to be addressed later. For now, replaceEscapedChars is only meant for processing
			 * identifiers, but it could be extended to work for strings as well.
			 */
			
			// The string wasn't changed, so realPos is the same as pos
			realPos = pos;
			
		} else {
			
			// Skip whichever char comes next.
			// just remove the backslash, keeping the following character
			selector = selector.substring(0, pos - 1) + selector.substring(pos);
			
			// pos is automatically advanced past the following character because the length
			// of selector before pos shrinks by 1.
			
			// Increase realPos to account for the escaped character.
			realPos = pos + 1;
			
		}
		
		return {
			pos: pos,
			realPos: realPos,
			selector: selector
		};
		
	}
	
	function hexToChar(h) {
		if(h > 0xFFFF) {
			h -= 0x10000;  
			return String.fromCharCode(0xD800 + (h >> 10), 0xDC00 + (h & 0x3FF));  
		} else return String.fromCharCode(h);
	}
	
	return replaceEscapedChars;
	
})();
	var parseCachableSelector = (function() {
	
	var cache = selectorCache.selectorLists;
	
	function parseCachableSelector(selector) {
		
		var pSel = cache[selector];
		
		if(!pSel) {
			pSel = parseSelector(selector);
			cache[selector] = pSel;
		}
		
		return pSel;
		
	}
	
	return parseCachableSelector;
	
})();
	
	// Library Object Definition
	var QuicksandParser = {
		
		/* Change libName if you would like error messages to display an alternate object for calling
		 * methods like enableExtended, enableCss4, and enableExtended. Please make sure that you
		 * implement these methods on your alternate object.
		 */
		libName: 'QuicksandParser',
		
		version: {
			major: 2,
			minor: 0,
			revision: 0,
			beta: true
		},
		
		parse: parseSelector,
		
		// allowInitialCombinator can be set to true to allow the selector to begin with a combinator.
		allowInitialCombinator: false,
		
		// allowTerminalCombinator can be set to true to allow the selector to end with a combinator.
		allowTerminalCombinator: false,
		
		cache: selectorCache,
		
		enableCache: function(tf) {
			/* Can be used to enable selector caching
			 * Please note that by enabling caching, you must make sure not to modify the returned selector object
			 * unless you want the modifications to be returned on subsequent calls. When caching is turned on
			 * a new object is not created for each call with the same selector. The object is created once and
			 * recycled after that, so any changes to the selector object will remain in the cache.
			 */
			if(tf === undefined) tf = true;
			if(tf) QuicksandParser.parse = parseCachableSelector;
			else QuicksandParser.parse = parseSelector;
			cacheEnabled = !!tf;
		},
		
		enableCss4: function(prefix) {
			// EXPIREMENTAL. See note on css4Enabled variable.
			if(!prefix) css4Enabled = true;
			else getPrefixObject(prefix).css4 = true;
		},
		
		disableCss4: function(prefix) {
			if(!prefix) css4Enabled = false;
			else getPrefixObject(prefix).css4 = false;
		},
		
		enableExtended: function(prefix) {
			if(!prefix) extendedEnabled = true;
			else getPrefixObject(prefix).extended = true;
		},
		
		disableExtended: function(prefix) {
			if(!prefix) extendedEnabled = false;
			else getPrefixObject(prefix).extended = false;
		},
		
		enableExperimental: function(prefix) {
			// EXPIREMENTAL. See note on css4Enabled variable.
			if(!prefix) experimentalEnabled = true;
			else getPrefixObject(prefix).experimental = true;
		},
		
		disableExperimental: function(prefix) {
			if(!prefix) experimentalEnabled = false;
			else getPrefixObject(prefix).experimental = false;
		},
		
		enableSubject: function(symbol) {
			// symbol is optional.
			if(symbol == '$') subjectMode = '$';
			else if(symbol == '!') subjectMode = '!';
			else if(symbol) throw 'QuicksandParser: Symbol not recognized (' + symbol + ') in enableSubject. Please use "$" or "!".';
			subjectEnabled = true;
		},
		
		disableSubject: function() {
			subjectEnabled = false;
		},
		
		addPseudoClass: function(identifier, options) {
			/* options:
			 * 		requireArgument:	true/false. Determines whether an argument is required. Default is false.
			 * 		extended:			true/false. Determines whether the pseudo-class is considered an extended feature. Default is false.
			 * 		css4:				true/false. Determines whether the pseudo-class is considered a CSS4 feature. Overrides extended.
			 * 							Default is false.
			 * 		experimental:		true/false. Determines whether the pseudo-class is considered an experimental feature.
			 * 							Overrides extended and css4. Default is false.
			 * 
			 * Note: Due to QuicksandParser's cache system, the extended, css4, and experimental flags cannot be changed on a second
			 * call to addPseudoClass. The requireArgument option can, however, be changed with a subsequent all using the same identifier.
			 */
			
			var pcId = pseudoClassTypes[identifier],
				preExisted = true;
			
			if(!pcId) {
				pcId = 100000 + (++nextCustomIdBase);
				preExisted = false;
			} else if(pcId < 100000) throw 'QuicksandParser: The pseudo-class cannot be overridden: ' + identifier;
			
			if(options) {
				
				// Do not allow changes in the pseudo-class id for pre-existing identifiers
				if(!preExisted) {
					if(options.experimental) pcId = -pcId;
					else if(options.css4) pcId += 40000;
					else if(options.extended) pcId += 90000;
				}
				
				if(options.requireArgument) requireArgument[identifier] = true;
				else if(options.requireArgument === false) requireArgument[identifier] = false; // allow this option to be changed back to false if it was set to true
				
			}
			
			pseudoClassTypes[identifier] = pcId;
			
			return pcId;
			
		},
		
		getPseudoClass: function(identifier) {
			return pseudoClassTypes[identifier];
		}
		
	};
	
	function getPrefixObject(prefix) {
		for(var i = 0; i < selectorPrefixes.length; i++) {
			if(selectorPrefixes[i].prefix == prefix) {
				return selectorPrefixes[i];
			}
		}
		var pObj = { prefix: prefix };
		selectorPrefixes.push(pObj);
		return pObj;
	}
	
	function trim(s) {
		if(s.trim) return s.trim();
		return s.replace(/^\s\s*/, '').replace(/\s\s*$/, '');
	}
	
	return QuicksandParser;
	
})();
	QuicksandParser.libName = 'Quicksand';
	QuicksandParser.enableCache();
	
	// include fast track selectors
	var setupFastTracks = (function() {
	
	var fastTrack = [ ],
		fastTrackSetup = {
			'^[\\w\\s\\,]+$': getTags,
			'^\\.[\\w\\-]+$': getClass
		};
	
	for(var i in fastTrackSetup) {
		if(fastTrackSetup.hasOwnProperty(i)) {
			fastTrack.push({
				regex: new RegExp(i),
				process: fastTrackSetup[i]
			});
		}
	}
	
	function setupFastTracks(selectorList) {
		// Returns true if fast tracks were set up or false if they weren't
		var str = selectorList.original, track;
		for(var i = 0; i < fastTrack.length; i++) {
			track = fastTrack[i];
			if(track.regex.test(str)) {
				selectorList.algorithm = [[
					{ call: track.process(trim(str)) }
				]];
				return true;
			}
		}
		return false;
	}
	
	function getBody() {
		return function(p) {
			var parent = p[0];
			if(parent == document || parent == documentElement) {
				return [ document.body ];
			} else {
				return [ ];
			}
		};
	}
	
	function getBodyAndTag(selector) {
		var matches = /^body\s+([\w]+)$/.exec(selector);
		return function(p) {
			var selection, parent = p[0];
			if(parent == document || parent == documentElement) {
				selection = [ ];
				fPush.apply(selection, document.body.getElementsByTagName(matches[1]));
				return selection;
			} else {
				return [ ];
			}
		};
	}
	
	function getTag(selector) {
		return function(p) {
			var selection = [ ];
			fPush.apply(selection, p[0].getElementsByTagName(selector));
			return selection;
		};
	}
	
	function getTags(selector) {
		if(~selector.indexOf(',')) return getEachTag(selector);
		var matches = selector.match(/\w+/g);
		if(matches.length == 1) {
			if(matches[0] == 'body') return getBody(selector);
			else return getTag(selector);
		} else if(matches.length == 2 && matches[0] == 'body') {
			return getBodyAndTag(selector);
		} else {
			return function(p) {
				var selection, curElements, tag, parent = p[0];
				curElements = [ ];
				fPush.apply(curElements, parent.getElementsByTagName(matches[0]));
				for(var i = 1; i < matches.length; i++) {
					tag = matches[i];
					p = curElements;
					curElements = [ ];
					for(var j = 0; j < p.length; j++) {
						fPush.apply(curElements, p[j].getElementsByTagName(tag));
					}
				}
				return removeDuplicates(curElements);
			};
		}
	}
		
	function getEachTag(selector) {
		var selectors = selector.split(/\s*\,\s*/),
			algorithm = [ ],
			reHasCombinator = /\w\s\w/;
		for(var i = 0; i < selectors.length; i++) {
			if(!reHasCombinator.test(selectors[i])) algorithm[i] = true; // true means to use getElementsByTagName
			else algorithm[i] = getTags(selectors[i]);
		}
		return function(p) {
			var selection = [ ], parent = p[0];
			for(var i = 0; i < algorithm.length; i++) {
				if(algorithm[i] === true) fPush.apply(selection, parent.getElementsByTagName(selectors[i]));
				else fPush.apply(selection, algorithm[i](p));
			}
			return selection;
		};
	}
	
	function getClass(selector) {
		var className = selector.substring(1);
		if(document.getElementsByClassName) {
			return function(p) {
				var selection = [ ];
				fPush.apply(selection, p[0].getElementsByClassName(selector.replace(/\./g, ' ')));
				return selection;
			};
		} else {
			var reHasClass = new RegExp('(^|\\s)' + className + '(\\s|$)');
			return function(p) {
				var allElements = p[0].getElementsByTagName('*'),
					selection = [ ], el;
				for(var i = 0, al = allElements.length; i < al; i++) {
					el = allElements[i];
					if(reHasClass.test(el.className)) {
						selection.push(el);
					}
				}
				return selection;
			}
		}
	}
	
	return setupFastTracks;
	
})();
	
	function warn(obj) {
	if(Quicksand.debugMode) {
		if(console && console.log) console.log('Quicksand (warning): ' + (obj.toString ? obj.toString() : obj));
	}
}

function Warning(s) {
	this._string = s;
}
Warning.prototype = {
	toString: function() { return this._string; }
};

function BrowserSupportWarning(options) {
	this._string = 'Browser support for ' + options.selector + ' may be limited.\n'
			+ 'Supported browsers:\n'
			+ 'Internet Explorer ' + options.ie
			+ ', Firefox ' + options.firefox
			+ ', Chrome ' + options.chrome
			+ ', Safari ' + options.safari
			+ ', Opera '  + options.opera;
	this.support = {
		ie: options.ie,
		firefox: options.firefox,
		chrome: options.chrome,
		safari: options.safari,
		opera: options.opera
	};
}

BrowserSupportWarning.prototype = new Warning();

	/* Performs any optimizations possible to make the selector one that can
 * be processed more quickly.
 */
var optimizeSelector = (function() {
	
	var attributeProperties = { };
	
	function optimizeSelector(selectorList) {
		
		var selector,
			
			// item selector
			item,
			
			// compound selector
			cSel;
		
		for(var i = 0; i < selectorList.length; i++) {
			selector = selectorList[i];
			for(var j = 0; j < selector.length; j++) {
				item = selector[j];
				if(!item.algorithm) {
					cSel = item.compoundSelector;
					if(cSel.pseudoClasses && splitAnyMatches(cSel, selectorList, i, j)) {
						i--;
						break;
					}
				}
			}
		}
		
		for(var i = 0; i < selectorList.length; i++) {
			selector = selectorList[i];
			for(var j = 0; j < selector.length; j++) {
				item = selector[j];
				if(!item.algorithm) {
					cSel = item.compoundSelector;
					if(cSel.type.name) optimizeType(cSel);
					if(cSel.attributes) optimizeAttributes(cSel);
					if(cSel.classes) optimizeClasses(cSel);
					if(cSel.pseudoClasses) optimizePseudoClasses(cSel, selectorList, i, j);
				}
			}
			
		}
		
	}
	
	function optimizeType(cSel) {
		// Convert tag names to uppercase
		cSel.type.name = cSel.type.name.toUpperCase();
	}
	
	function optimizeAttributes(cSel) {
		var attributes = cSel.attributes, attribute;
		for(var i = 0; i < attributes.length; i++) {
			attribute = attributes[i];
			switch(attribute.name) {
				
				case 'id':
					// Replace [id=X] selectors with #X selectors
					if(!cSel.id && attribute.operator == EQUALS_ATTRIBUTE_OPERATOR) {
						cSel.id = attribute.value;
						attributes.splice(i, 1);
						i--;
					}
					break;
					
				case 'class':
					// Replace [class~=X] selectors with .X selectors
					if(attribute.operator == CONTAINS_WORD_ATTRIBUTE_OPERATOR) {
						if(!cSel.classes) cSel.classes = [ ];
						cSel.classes.push(attribute.value);
						attributes.splice(i, 1);
						i--;
					}
					break;
			}
			if(attributeProperties[attribute.name]) attribute.property = attributeProperties[attribute.name];
		}
		if(attributes.length == 0) cSel.attributes = undefined;
	}
	
	function optimizeClasses(cSel) {
		// Generate regular expressions for each class
		var regexes = [ ];
		for(var i = 0; i < cSel.classes.length; i++) {
			regexes.push(new RegExp('(^|\s)' + cSel.classes[i] + '(\s|$)'));
		}
		cSel.classes_regexes = regexes;
	}
	
	function splitAnyMatches(cSel, selectorList, sIndex, iIndex) {
		// selectorList, sIndex, and iIndex are used by optimizeMatches.
		
		var pseudoClasses = cSel.pseudoClasses, didSplit = false;
		
		for(var i = 0; i < pseudoClasses.length; i++) {
			if(pseudoClasses[i].pseudoClass == MATCHES_PSEUDOCLASS) {
				// TODO: When :nth and :nth-last are fixed (see note in filterFilter.jsx) and when :matches returns in document order, then they can be allowed together.
				if(cSel.filter) throw 'Quicksand: The :nth or :nth-last pseudo-classes are not allowed with :matches.';
				optimizeMatches(cSel, pseudoClasses[i], selectorList, sIndex, iIndex);
				didSplit = true;
				break;
			}
		}
		
		return didSplit;
		
	}
	
	function optimizePseudoClasses(cSel) {
		// selectorList, sIndex, and iIndex are used by optimizeMatches.
		
		var pseudoClasses = cSel.pseudoClasses, pc, removePc;
		
		for(var i = 0; i < pseudoClasses.length; i++) {
			pc = pseudoClasses[i];
			removePc = false;
			switch(pc.pseudoClass) {
				
				case NTH_CHILD_PSEUDOCLASS:
					// Remove :nth-child(an+b) pseudo-class when a = 1 and b = 0
					if(pc.a == 1 && pc.b == 0) {
						removePc = true;
					}
					break;
				
				case NOT_PSEUDOCLASS:
					optimizeNot(cSel, pc);
					removePc = true;
					break;
				
				case ANY_LINK_PSEUDOCLASS:
					/* Note: The first draft has minimal information on how any-link is supposed to behave.
					 * From the little that's there and from looking at the behavior of -moz-any-link, it seems
					 * like it's just supposed to select any link, regardless of whether it has been visited.
					 */
				case LINK_PSEUDOCLASS:
					if(!cSel.attributes) cSel.attributes = [ ];
					cSel.attributes.push({
						name: 'href',
						operator: HAS_ATTRIBUTE_OPERATOR
					});
					removePc = true;
					break;
				case VISITED_PSEUDOCLASS:
					// All links will be treated as unvisited due to privacy considerations and browser security restrictions.
					cSel.noResults = true;
					removePc = true;
					break;
				case LOCAL_LINK_PSEUDOCLASS:
					if(!cSel.attributes) cSel.attributes = [ ];
					if(pc.pathLevels === undefined) {
						cSel.attributes.push({
							name: 'href',
							operator: LOCAL_LINK_EXACT_ATTRIBUTE_OPERATOR
						});
					} else {
						cSel.attributes.push({
							name: 'href',
							operator: LOCAL_LINK_PARTIAL_ATTRIBUTE_OPERATOR,
							value: pc.pathLevels
						});
					}
					removePc = true;
					break;
					
				case TARGET_PSEUDOCLASS:
					cSel.optimizedSelPath_target = true;
					break;
				case FOCUS_PSEUDOCLASS:
					// Note: filterFocus uses document.activeElement, which lacks support in old browsers.
					// It has been determined, however, that support is extensive enough for Quicksand to support this feature.
					// Support information from: https://developer.mozilla.org/en/DOM/document.activeElement
					warn(new BrowserSupportWarning({
						selector: ':focus',
						chrome: 2,
						firefox: 3,
						ie: 4,
						opera: 9.6,
						safari: 4
					}));
					cSel.optimizedSelPath_focus = true;
					break;
					
				case ROOT_PSEUDOCLASS:
					if(cSel.type.name == '*') cSel.type.name = 'HTML';
					else if(cSel.type.name != 'HTML') cSel.noResults = true;
					break;
					
				case COLUMN_PSEUDOCLASS:
					optimizeColumnSelector(pc.selector);
					break;
								
			}
			
			if(removePc) {
				pseudoClasses.splice(i, 1);
				i--;
			}
			
		}
		
		if(pseudoClasses.length == 0) cSel.pseudoClasses = undefined;
		
	}
	
	function optimizeNot(cSel, pc) {
		var csl = optimizeCompoundSelectorList(pc.selector),
			cSelTypeName = cSel.type.name,
			notCSel;
		for(var i = 0; i < csl.length; i++) {
			notCSel = csl[i];
			if(notCSel.type != undefined) {
				if(cSelTypeName != '*') {
					if(cSelTypeName == notCSel.type.name.toUpperCase()) {
						// The selector should return no results.
						cSel.noResults = true;
					} else {
						// cSel's tag name doesn't match notCSel's tag name, so the :not tag name will be excluded implicitly
						notCSel.type = undefined;
					}
				}
			}
			// TODO: Do more checks to speed up nonsensical things, like #my_id:not(#my_id)
		}
		if(cSel.not) fPush.apply(cSel.not, csl); // permit multiple not pseudo-classes on the same compound selector	
		else cSel.not = csl;
	}
	
	function optimizeMatches(cSel, pc, selectorList, sIndex, iIndex) {
		// sIndex: the index of the current selector in the selectorList
		// iIndex: the index of the current item selector in the current selector
		
		var csl = optimizeCompoundSelectorList(pc.selector),
			cSelTypeName = cSel.type.name,
			matchesCSel, newSelector, newSelectors = [ ], newCSel, newItem,
			curSelector = selectorList[sIndex],
			skip;
		
		for(var i = 0; i < csl.length; i++) {
			
			matchesCSel = csl[i];
			skip = false;
			
			if(matchesCSel.type != undefined) {
				if(cSel.type.name == '*') {
					if(csl.length == 1) cSel.type.name = matchesCSel.type.name;
				} else if(cSelTypeName == matchesCSel.type.name.toUpperCase()) {
					// There's no reason to double check the tag name
					matchesCSel.type = undefined;
				} else {
					// The tag names don't match, so skip this matches selector
					skip = true;
				}
			}
			if(matchesCSel.id != undefined) {
				if(cSel.id == matchesCSel.id) {
					// There's no reason to double check the id
					matchesCSel.type = undefined;
				} else {
					// The ids don't match, so skip this matches selector
					skip = true;
				}
			}
			
			if(!skip) {
				// build new selector lists to replace current one, expanding :matches
				
				newCSel = {
					type: { name: cSel.type.name },
					id: cSel.id || matchesCSel.id,
					classes: copyArray(cSel.classes),
					pseudoClasses: copyArrayExcept(cSel.pseudoClasses, pc),
					attributes: copyArray(cSel.attributes)
				};
				if(matchesCSel.type) newCSel.type.name = matchesCSel.type.name;
				if(matchesCSel.classes) newCSel.classes = addToArray(newCSel.classes, matchesCSel.classes);
				if(matchesCSel.pseudoClasses) newCSel.pseudoClasses = addToArray(newCSel.pseudoClasses, matchesCSel.pseudoClasses);
				if(matchesCSel.attributes) newCSel.attributes = addToArray(newCSel.attributes, matchesCSel.attributes);
				
				newItem = {
					combinator: curSelector[iIndex].combinator,
					compoundSelector: newCSel
				};
				
				newSelector = [ ];
				for(var j = 0; j < iIndex; j++) {
					newSelector.push(curSelector[j]);
				}
				newSelector.push(newItem);
				for(var j = iIndex + 1; j < curSelector.length; j++) {
					newSelector.push(curSelector[j]);
				}
				newSelectors.push(newSelector);
				
			}
			
		}
		
		// Update the selector list with the new selectors
		newSelectors.unshift(sIndex, 1);
		fSplice.apply(selectorList, newSelectors);
		
	}
	
	function optimizeCompoundSelectorList(sl) {
		if(sl.optimizedCSL) return sl.optimizedCSL;
		var sel, item, cSel, cSelList = [ ];
		for(var i = 0; i < sl.length; i++) {
			sel = sl[i];
			item = sel[0];
			cSel = item.compoundSelector;
			if(sel.length > 1 || item.combinator.type != DESCENDANT_COMBINATOR) throw 'Quicksand: Combinators are not allowed as arguments in pseudo-classes.';
			if(cSel.type.name == undefined) cSel.type = undefined;
			if(cSel.attributes) optimizeAttributes(cSel);
			if(cSel.classes) optimizeClasses(cSel);
			if(cSel.pseudoClasses) optimizePseudoClasses(cSel);
			cSelList.push(cSel);
		}
		sl.optimizedCSL = cSelList;
		return cSelList;
	}
	
	function optimizeColumnSelector(sl) {
		var sel, item, cSel;
		for(var i = 0; i < sl.length; i++) {
			sel = sl[i];
			for(var j = 0; j < sel.length; j++) {
				item = sel[j];
				cSel = item.compoundSelector;
				// The selector can only select COL elements
				if(cSel.type.name == '*') cSel.type.name = 'COL';
				// toUpperCase() is needed below because no optimizations have yet been performed on this selector-list 
				else if(cSel.type.name.toUpperCase() != 'COL') cSel.noResults = true;
			}
		}
		preProcessSelectorList(sl);
	}
	
	function copyArray(arr) {
		return arr ? arr.slice(0, arr.length) : undefined;
	}
	
	function copyArrayExcept(arr, exception) {
		var arr2 = [ ], item;
		for(var i = 0; i < arr.length; i++) {
			item = arr[i];
			if(item != exception) arr2.push(item);
		}
		if(arr2.length == 0) return undefined;
		return arr2;
	}
	
	function addToArray(arr1, arr2) {
		if(!arr1) return arr2.slice(0, arr2.length);
		fPush.apply(arr1, arr2);
		return arr1;
	}
	
	if(!supportsHasAttribute) {
		attributeProperties = {
			'class': 'className'
		};
	}
	
	return optimizeSelector;
	
})();
	var qSelect = (function() {
	
	function qSelect(selectorList, root, scope) {
		
		var algorithm = selectorList.algorithm,
			curElements,
			selAlg, item, args, selection = [ ];
		
		for(var i = 0; i < algorithm.length; i++) {
			selAlg = algorithm[i];
			curElements = [ root ];
			for(var j = 0; j < selAlg.length; j++) {
				item = selAlg[j];
				args = [ curElements, scope ];
				if(item.arguments) fUnshift.apply(args, item.arguments)
				curElements = item.call.apply(null, args);
			}
			fPush.apply(selection, curElements);
		}
		
		if(algorithm.length > 1) {
			selection = sortElements(selection);
			selection = removeDuplicates(selection);
		}
		
		if(scope) selection = filterDescendants(selection, scope);
		
		return selection;
		
	}
	
	function filterDescendants(selection, ancestor) {
		// TODO: This can probably be sped up.
		var newSelection = [ ], el, p, lastP;
		for(var i = 0; i < selection.length; i++) {
			el = selection[i];
			p = el.parentNode;
			if(p == lastP || isDescendant(p, ancestor)) {
				lastP = p;
				newSelection.push(el);
			}
		}
		return newSelection;
	}
	
	function isDescendant(p, ancestor) {
		if(!p) return false;
		do {
			if(p == ancestor) return true;
		} while(p = p.parentNode);
		return false;
	}
	
	return qSelect;
	
})();

	var removeDuplicates = (function() {
	
	function removeDuplicates(curElements) {
		
		if(curElements.length <= 1) return curElements;
		
		var el, id, newCurElements = [ ], cache = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			id = el._qs_elId;
			if(!id) {
				id = el._qs_elId = ++nextElId;
				newCurElements.push(el);
				cache[id] = true;
			} else if(!cache[id]) {
				newCurElements.push(el);
				cache[id] = true;
			}
		}
		
		return newCurElements;
		
	}
	
	return removeDuplicates;
	
})();
	function sortElements(curElements) {
	
	if(curElements.length <= 1) return curElements;
	
	var el, id, newCurElements = [ ], elIds = [ ],
		all, tagName = curElements[0].tagName,
		elId;
	
	for(var i = 0; i < curElements.length; i++) {
		el = curElements[i];
		if(tagName != '*' && tagName != el.tagName) tagName = '*';
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		elIds[elId] = true;
	}
	
	all = curElements[0].ownerDocument.getElementsByTagName(tagName)
	
	for(var i = 0, l = all.length; i < l; i++) {
		el = all[i];
		elId = el._qs_elId;
		if(elId && elIds[elId]) newCurElements.push(el);
	}
	
	return newCurElements;
	
}
	function isAncestor(ancestor, el) {
	var p = el;
	while(p = p.parentNode) {
		if(p == ancestor) return true;
	}
	return false;
}
	// Creates and caches an array of functions which can be called
// to select the elements for this selector list
var processSelectorList = (function() {
	
	var curCombinator;
	
	var filterAdjacentSiblings = (function() {
	
	function filterAdjacentSiblings(el, ch) {
		var curElements = [ ], cel, pel = el.parentNode;
		for(var i = 0, chl = ch.length; i < chl; i++) {
			cel = ch[i];
			if(cel.parentNode == pel && areAdjacentSiblings(el, cel)) {
				curElements.push(cel);
				el = cel;
			}
		}
		return curElements;
	}
	
	function areAdjacentSiblings(el1, el2) {
		// el2 should be the next element after el1 in the document
		while(el1 = el1.nextSibling) {
			if(el1 == el2) return true;
			if(el1.nodeType == 1) return false;
		}
		return false;
	}
	
	return filterAdjacentSiblings;
	
})();var filterAttributes = (function() {
	
	var filterHas;
	
	function filterAttributes(attributes, algorithm) {
		
		var attribute, name, value, caseInsensitive,
			
			// safeName will be the attribute name which should be used for getAttribute (which needs to be the property name in IE)
			safeName;
		
		for(var i = 0; i < attributes.length; i++) {
			attribute = attributes[i];
			name = attribute.name;
			value = attribute.value;
			caseInsensitive = !!attribute.caseInsensitive;
			safeName = attribute.property || name;
			if(caseInsensitive && value) value = value.toLowerCase();
			switch(attribute.operator) {
				
				case HAS_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: filterHas,
						arguments: [ name ]
					});
					break;
				case EQUALS_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterEqualsCI : filterEquals,
						arguments: [ safeName, value ]
					});
					break;
				case STARTS_WITH_DASH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterStartsWithCI : filterStartsWith,
						arguments: [ safeName, value + '-' ]
					});
					break;
				case STARTS_WITH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterStartsWithCI : filterStartsWith,
						arguments: [ safeName, value ]
					});
					break;
				case ENDS_WITH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterEndsWithCI : filterEndsWith,
						arguments: [ safeName, value ]
					});
					break;
				case CONTAINS_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterContainsCI : filterContains,
						arguments: [ safeName, value ]
					});
					break;
				case CONTAINS_WORD_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterContainsWordCI : filterContainsWord,
						arguments: [ safeName, value ]
					});
					break;
				
				case DOESNT_EQUAL_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntEqualCI : filterDoesntEqual,
						arguments: [ safeName, value ]
					});
					break;
				case DOESNT_CONTAIN_WORD_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntContainWordCI : filterDoesntContainWord,
						arguments: [ safeName, value ]
					});
					break;
				case DOESNT_START_WITH_DASH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntStartWithCI : filterDoesntStartWith,
						arguments: [ safeName, value + '-' ]
					});
					break;
				case DOESNT_START_WITH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntStartWithCI : filterDoesntStartWith,
						arguments: [ safeName, value ]
					});
					break;
				case DOESNT_END_WITH_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntEndWithCI : filterDoesntEndWith,
						arguments: [ safeName, value ]
					});
					break;
				case DOESNT_CONTAIN_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: caseInsensitive ? filterDoesntContainCI : filterDoesntContain,
						arguments: [ safeName, value ]
					});
					break;
				
				// Used by the :local-link pseudo-class
				case LOCAL_LINK_PARTIAL_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: filterPartialLocalLink,
						arguments: [ safeName, value ]
					});
					break;
				case LOCAL_LINK_EXACT_ATTRIBUTE_OPERATOR:
					algorithm.push({
						call: filterExactLocalLink,
						arguments: [ safeName ]
					});
					break;
				
				default: throw 'Quicksand: Attribute operator not implemented: ' + attribute.operator;
				
			}
			
		}
		
	}
	
	if(supportsHasAttribute) {
		
		filterHas = function(name, curElements) {
			var newCurElements = [ ], el;
			for(var i = 0; i < curElements.length; i++) {
				el = curElements[i];
				if(el.hasAttribute(name)) {
					newCurElements.push(el);
				}
			}
			return newCurElements;
		}
		
	} else {
		
		filterHas = function(name, curElements) {
			var newCurElements = [ ], el, n;
			for(var i = 0; i < curElements.length; i++) {
				el = curElements[i];
				n = el.getAttributeNode(name);
				if(n && n.specified) newCurElements.push(el);
			}
			return newCurElements;
		}
		
	}
	
	function filterEquals(name, value, curElements) {
		var newCurElements = [ ], el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			if(el.getAttribute(name, 2) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterEqualsCI(name, value, curElements) {
		var newCurElements = [ ], el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.toLowerCase() == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntEqual(name, value, curElements) {
		var newCurElements = [ ], el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			if(el.getAttribute(name, 2) != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntEqualCI(name, value, curElements) {
		var newCurElements = [ ], el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.toLowerCase() != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterStartsWith(name, value, curElements) {
		var newCurElements = [ ],
			vl = value.length, s, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.substring(0, vl) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterStartsWithCI(name, value, curElements) {
		var newCurElements = [ ],
			vl = value.length, s, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.toLowerCase().substring(0, vl) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntStartWith(name, value, curElements) {
		var newCurElements = [ ],
			vl = value.length, s, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.substring(0, vl) != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntStartWithCI(name, value, curElements) {
		var newCurElements = [ ],
			vl = value.length, s, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.toLowerCase().substring(0, vl) != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterEndsWith(name, value, curElements) {
		var newCurElements = [ ],
			s, vl = value.length, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.substring(s.length - vl) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterEndsWithCI(name, value, curElements) {
		var newCurElements = [ ],
			s, vl = value.length, el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.toLowerCase().substring(s.length - vl) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntEndWith(name, value, curElements) {
		var newCurElements = [ ],
			s, vl = value.length;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.substring(s.length - vl) != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntEndWithCI(name, value, curElements) {
		var newCurElements = [ ],
			s, vl = value.length;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.toLowerCase().substring(s.length - vl) != value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterContains(name, value, curElements) {
		var newCurElements = [ ],
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.indexOf(value) > -1) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterContainsCI(name, value, curElements) {
		var newCurElements = [ ],
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && s.toLowerCase().indexOf(value) > -1) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntContain(name, value, curElements) {
		var newCurElements = [ ],
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.indexOf(value) == -1) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntContainCI(name, value, curElements) {
		var newCurElements = [ ],
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || s.toLowerCase().indexOf(value) == -1) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterContainsWord(name, value, curElements) {
		var newCurElements = [ ],
			re = new RegExp('(^|\s)' + value + '(\s|^)'),
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s && (s == value || re.test(s))) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterContainsWordCI(name, value, curElements) {
		var newCurElements = [ ],
			re = new RegExp('(^|\s)' + value + '(\s|^)'),
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(s) {
				s = s.toLowerCase();
				if(s && (s == value || re.test(s))) {
					newCurElements.push(el);
				}
			}
		}
		return newCurElements;
	}
	
	function filterDoesntContainWord(name, value, curElements) {
		var newCurElements = [ ],
			re = new RegExp('(^|\s)' + value + '(\s|^)'),
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s || (s != value && !re.test(s))) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterDoesntContainWordCI(name, value, curElements) {
		var newCurElements = [ ],
			re = new RegExp('(^|\s)' + value + '(\s|^)'),
			el, s;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// Using 2 as the second argument can help speed up IE7 considerably
			s = el.getAttribute(name, 2);
			if(!s) newCurElements.push(el);
			else {
				s = s.toLowerCase();
				if((s != value && !re.test(s))) {
					newCurElements.push(el);
				}
			}
		}
		return newCurElements;
	}
	
	function filterPartialLocalLink(name, value, curElements) {
		var newCurElements = [ ],
			el, s;
		value = getLocalUrl(value);
		if(!value) return [ ];
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			s = el[name];
			if(s && urlStartsWith(s, value)) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function filterExactLocalLink(name, curElements) {
		var newCurElements = [ ],
			el, s;
		value = getLocalUrl();
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			s = el[name];
			if(s && removeFragment(s) == value) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
	
	function urlStartsWith(url, part) {
		url = removeFragment(removeFragment(url), '?');
		var loc = url.indexOf(':/'), end;
		if(loc == -1) return false;
		loc += 2;
		while(url.charAt(loc) == '/') loc++;
		end = loc + part.length;
		return url.substring(loc, end) == part && (url.length == end || url.charAt(end) == '/');
	}
	
	function removeFragment(url, startChar) {
		var loc = url.indexOf(startChar || '#');
		if(loc == -1) return url;
		return url.substring(0, loc);
	}
	
	// This method was moved from optimizeSelector to here due to the fact that if the value is cached
	// then history.pushState can break it. The local url needs to be calculated each time the :local-link
	// pseudo-class is used in order to keep up with a dynamic document location. 
	function getLocalUrl(pathLevels) {
		/* Note: Due to the implementation of this function, the :local-link selector will not
		 * work across frames. There are some other selectors that could also return unexpected
		 * results across frames, such as :first-child which will probably return the documentElement,
		 * since the current implemenation only tests to make sure the current frame's documentElement
		 * is not the element, but it doesn't test across frames.
		 * TODO: There are three potential approaches that could be taken.
		 *   (1) Fix this problem so that Quicksand will work across frames. However, this solution will
		 *       come at a speed cost.
		 *   (2) Set up Quicksand to create a new instance of the Quicksand object inside a frame on which
		 *       it is called, so that the new internal version of Quicksand can be used to test elements
		 *       across frames and do so accurately and quickly. This solution will come at a memory cost,
		 *       but the cost should be very minor.
		 *   (3) Simply document that Quicksand is not intended for cross-frame usage and recommend that
		 *       users include Quicksand within any frames in which they want to select elements.
		 */
		
		if(pathLevels === undefined) return location.href.substring(0, location.href.length - (location.hash || '').length);
		else if(pathLevels == 0) return location.hostname;
		
		var pathParts = location.pathname.split('/'), localUrl;
		
		if(pathLevels > pathParts.length) {
			// Note: The first draft of Selectors 4 makes it sound like :local-link should never match
			// if there are too many path levels, but it isn't clear.
			// TODO: Reevaluate this behavior when the next draft comes out.
			return false;
		}
		
		localUrl = location.hostname;
		for(var i = 1; i <= pathLevels; i++) {
			localUrl += '/' + pathParts[i];
		}
		
		return localUrl;
		
	}
	
	return filterAttributes;
	
})();var filterGeneralSiblings = (function() {
	
	function filterGeneralSiblings(el, ch) {
		var curElements = [ ], cel, pel = el.parentNode;
		for(var i = 0, chl = ch.length; i < chl; i++) {
			cel = ch[i];
			if(cel.parentNode == pel && areGeneralSiblings(el, cel)) {
				curElements.push(cel);
				el = cel;
			}
		}
		return curElements;
	}
	
	function areGeneralSiblings(el1, el2) {
		// el2 should come after el1 in the document
		while(el1 = el1.nextSibling) {
			if(el1 == el2) return true;
		}
		return false;
	}
	
	return filterGeneralSiblings;
	
})();function hasClasses(className, regexes) {
	for(var i = 0; i < regexes.length; i++) {
		if(!regexes[i].test(className)) return false;
	}
	return true;
}function isAdjacentSibling(elA, elB) {
	// Checks to see if elB is the element right after elA
	while(elA = elA.nextSibling) {
		if(elA.nodeType == 1) return elA == elB;
	}
	return false;
}function isGeneralSibling(elA, elB) {
	// Checks to see if elB is a sibling element following elA
	if(elA.parentNode != elB.parentNode) return false;
	while(elA = elA.nextSibling) {
		if(elA == elB) return true;
	}
	return false;
}var processCompoundSelector = (function() {
	
	function processCompoundSelector(item, algorithm) {
		
		var cSel = item.compoundSelector;
		
		if(cSel.noResults) {
			// The selector should return no results
			algorithm.push({ call: returnEmpty });
			return;
		}
		
		if(cSel.id) {
			if(cSel.type.name != '*' || cSel.classes) selectByPath_idPlus(item, algorithm);
			else selectByPath_id(item, algorithm);
		}
		else if(cSel.classes && cSel.type.name != '*') selectByPath_tagAndClasses(item, algorithm);
		else if(cSel.type.name != '*') selectByPath_tagName(item, algorithm);
		else if(cSel.classes) selectByPath_classes(item, algorithm);
		else if(cSel.optimizedSelPath_target) selectByPath_target(item, algorithm);
		else selectByPath_tagName(item, algorithm);
		
		if(cSel.attributes) filterAttributes(cSel.attributes, algorithm);
		if(cSel.pseudoClasses) filterPseudoClasses(cSel.pseudoClasses, algorithm);
		if(cSel.not) filterNot(cSel.not, algorithm);
		// Filters must be done at the end of the algorithm
		if(cSel.filter) filterFilter(cSel.filter, algorithm);
		
	}
	
	return processCompoundSelector;
	
})();var processSelector = (function() {
	
	function processSelector(selector) {
		
		var item, algorithm = [ ], iAlg, subjectMode = false, subjectModeSwitch = false;
		
		for(var i = 0; i < selector.length; i++) {
			
			if(subjectModeSwitch) subjectMode = true;
			
			// A combinator / compound selector pair
			item = selector[i];
			
			if(!item.algorithm) {
				/* Combinator / compound selector pairs may be cached individually from the full
				 * selector list, so check to see if this compound selector has already been processed.
				 */
				
				// Create a temporary array of functions to call for this compound selector.
				// This array is only defined temporarily (instead of on the item object) in case there
				// is an error thrown during its definition, in which case the partially created array
				// should not be cached for later use.
				iAlg = [ ];
				processCompoundSelector(item, iAlg);
				
				// Now that the array has been created successfully, cache it for later use.
				item.algorithm = iAlg;				
				
				if(item.compoundSelector.subject) subjectModeSwitch = true;
				
			}
			
			if(subjectMode) {
				// A previous compound selector contained a subject selector.
				item.algorithm = [{
					call: subjectSelect,
					arguments: [ item.algorithm ]
				}];
			}
			
			// Push the functions for this combinator onto the selector's algorithm array
			fPush.apply(algorithm, item.algorithm);
			
		}
		
		if(subjectMode) {
			algorithm.push({
				call: zToElements
			});
		}
		
		if(selector.length > 1) algorithm.push({ call: removeDuplicates });
		
		return algorithm;
				
	}
	
	function subjectSelect(algorithm, z) {
		// z is either an array of subject element / current element matchings or
		// (if this is the first compound selector after the subject selector) z
		// is an array of current elements which are the subject elements.
		
		if(z.length == 0) return [ ];
		
		var newZ, resElements;
		
		if(!z[0].current) {
			newZ = [ ];
			for(var i = 0; i < z.length; i++) {
				newZ.push({
					subject: z[i],
					current: z[i]
				});
			}
			z = newZ;
		}
		
		newZ = [ ];
		for(var i = 0; i < z.length; i++) {
			resElements = resolveAlgorithm(algorithm, z[i].current);
			for(var j = 0; j < resElements.length; j++) {
				newZ.push({
					subject: z[i].subject,
					current: resElements[j]
				});
			}
		}
		
		return newZ;
		
	}
	
	function resolveAlgorithm(algorithm, parent) {
		
		var curElements = [ parent ],
			item, args, selection = [ ];
		
		for(var j = 0; j < algorithm.length; j++) {
			item = algorithm[j];
			args = [ curElements ];
			if(item.arguments) fUnshift.apply(args, item.arguments)
			curElements = item.call.apply(null, args);
		}
		
		return curElements;
		
	}
	
	function zToElements(z) {
		var curElements = [ ];
		for(var i = 0; i < z.length; i++) {
			curElements.push(z[i].subject);
		}
		return curElements;
	}
	
	return processSelector;
	
})();
function returnEmpty() {
	return [ ];
}
var filterFilter = (function() {
	/* TODO: Get :nth and :nth-last working other places instead of just at the end.
	 * This filter property of a compound selector is sort of an ad-hoc property to get
	 * :nth and :nth-last working at the end of a compound selector.
	 * Ideally, they could work anywhere in a compound selector, and any simple selectors
	 * before the filter will be pre-filtered before the :nth or :nth-last pseudo-classes
	 * are applied and any simple selectors after the filter will be post-filtered.
	 * For instance:
	 *   A. div:nth(even).example	=> selects all divs, then filters the even ones, then filters out the class "example"
	 *   B. div.example:nth(even)	=> selects all divs with class "example", then filters the even ones
	 * 
	 * So for the elements below:
	 *   <div>1<div><div class="example">2</div><div>3</div><div>4</div><div class="example">5</div>
	 * 
	 * A. would select div 2
	 * B. would select div 5
	 * 
	 * This would require a fair amount of work, but it should be doable and not too hard. Even though
	 * Quicksand does not work linearly (for instance, it is set up to select by tag and class first if
	 * they're available, so currently A would select by div and .example before looking at the pseudo-classes)
	 * some work could be done to keep these non-linear optimizations while returning the correct results
	 * for :nth and :nth-last pseudo-classes.
	 */
	
	function filterNth(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element number starting at 1
		elNum,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ];
	
	for(var i = 0; i < curElements.length; i++) {
		
		cel = el = curElements[i];
			
		elNum = i + 1;
		
		// Add element if it fits the constraints
		if(a == 0) {
			if(elNum == b) newCurElements.push(cel);
		} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
			newCurElements.push(cel)
		}
		
	}
	
	return newCurElements;
	
}
function filterNthLast(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element number starting at 1
		elNum = 0,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ];
	
	for(var i = curElements.length - 1; i >= 0; i--) {
		
		cel = el = curElements[i];
		
		elNum++;
		
		// Add element if it fits the constraints
		if(a == 0) {
			if(elNum == b) newCurElements.push(cel);
		} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
			newCurElements.push(cel)
		}
		
	}
	
	return newCurElements;
	
}

	
	function filterFilter(filter, algorithm) {
		
		switch(filter.type) {
			
			case NTH_PSEUDOCLASS:
				algorithm.push({
					call: filterNth,
					arguments: [ filter.a, filter.b ]
				});
				break;
			case NTH_LAST_PSEUDOCLASS:
				algorithm.push({
					call: filterNthLast,
					arguments: [ filter.a, filter.b ]
				});
				break;
			
			default: throw 'Quicksand: Filter not implemented: ' + filter.type;
			
		}
		
	}
	
	return filterFilter;
	
})();var filterNot = (function() {
	
	function doFilterNegateAlgorithm(isAlgorithm, curElements) {
	var newCurElements = [ ], isElements = curElements, item, args, isElementsHash = [ ], elId, el;
	for(var i = 0; i < isAlgorithm.length; i++) {
		item = isAlgorithm[i];
		args = [ isElements ];
		if(item.arguments) fUnshift.apply(args, item.arguments);
		isElements = item.call.apply(null, args);
	}
	for(var i = 0; i < isElements.length; i++) {
		el = isElements[i];
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		isElementsHash[elId] = true;
	}
	for(var i = 0; i < curElements.length; i++) {
		el = curElements[i];
		if(!isElementsHash[el._qs_elId]) newCurElements.push(el);
	}
	return newCurElements;
}
var filterNotAttributes = (function() {
	
	function filterNotAttributes(attributes, algorithm) {
		var isAlgorithm = [ ];
		filterAttributes(attributes, isAlgorithm);
		algorithm.push({
			call: doFilterNegateAlgorithm,
			arguments: [ isAlgorithm ]
		});
	}
		
	return filterNotAttributes;
	
})();var filterNotClasses = (function() {
	
	function filterNotClasses(regexes, algorithm) {
		algorithm.push({
			call: doFilterNotClasses,
			arguments: [ regexes ]
		});
	}
	
	function doFilterNotClasses(regexes, curElements) {
		var newCurElements = [ ], el;
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(!hasClasses(el.className, regexes)) {
				newCurElements.push(el);
			}
		}
		return newCurElements;
	}
		
	return filterNotClasses;
	
})();var filterNotId = (function() {
	
	function filterNotId(id, algorithm) {
		algorithm.push({
			call: doFilterNotId,
			arguments: [ id ]
		});
	}
	
	function doFilterNotId(id, curElements) {
		var newCurElements = [ ];
		for(var i = 0; i < curElements.length; i++) {
			if(curElements[i].id != id) {
				newCurElements.push(curElements[i]);
			}
		}
		return newCurElements;
	}
		
	return filterNotId;
	
})();var filterNotPseudoClasses = (function() {
	
	function filterNotPseudoClasses(pseudoClasses, algorithm) {
		var isAlgorithm = [ ];
		filterPseudoClasses(pseudoClasses, isAlgorithm);
		algorithm.push({
			call: doFilterNegateAlgorithm,
			arguments: [ isAlgorithm ]
		});
	}
		
	return filterNotPseudoClasses;
	
})();var filterNotTagName = (function() {
	
	function filterNotTagName(tagName, algorithm) {
		algorithm.push({
			call: doFilterNotTagName,
			arguments: [ tagName.toUpperCase() ]
		});
	}
	
	function doFilterNotTagName(tagName, curElements) {
		var newCurElements = [ ];
		for(var i = 0; i < curElements.length; i++) {
			if(curElements[i].tagName != tagName) {
				newCurElements.push(curElements[i]);
			}
		}
		return newCurElements;
	}
		
	return filterNotTagName;
	
})();
	
	function filterNot(notSelectors, algorithm) {
		var sel;
		for(var i = 0; i < notSelectors.length; i++) {
			sel = notSelectors[i];
			if(sel.id) filterNotId(sel.id, algorithm);
			if(sel.type) filterNotTagName(sel.type.name, algorithm);
			if(sel.classes_regexes) filterNotClasses(sel.classes_regexes, algorithm);
			if(sel.pseudoClasses) filterNotPseudoClasses(sel.pseudoClasses, algorithm);
			if(sel.attributes) filterNotAttributes(sel.attributes, algorithm);
		}
	}
	
	return filterNot;
	
})();var filterPseudoClasses = (function() {
	// NOTE: The NOT_PSEUDOCLASS is not filtered here. It is filtered in filterNot.
	
	var filterChecked = (function() {
	
	function filterChecked(value, curElements) {
		
		var el, newElements = [ ], type;
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el.checked === value) {
				type = el.type;
				// If value is false, make sure type is either radio or checkbox, otherwise
				// other input elements (like text boxes) will be returned also (for :unchecked).
				// The check is not needed when value is true (:checked) becaus if an element
				// has it's checked property set to true we can assume someone's using it's checked
				// value in a useful way -- so we should assume that it is checked.
				// TODO: Are there any other valid tags or input types that should be returned
				// by :unchecked? Particularly any new ones in HTML5?
				if(value || type == 'radio' || type == 'checkbox') newElements.push(el);
			}
		}
		
		return newElements;
		
	}
	
	return filterChecked;
	
})();
var filterColumn = (function() {
	
	function filterColumn(selectorList, curElements) {
		
		var el, newCurElements = [ ], cache = [ ], cellRange, tagName,
			cols, col,
			colsInfo = [ ], colInfo, colRange,
			table;
		
		if(curElements.length == 0) return [ ];
		
		cols = qSelect(selectorList, curElements[0].ownerDocument);
		if(cols.length == 0) return [ ];
		
		for(var i = 0; i < cols.length; i++) {
			col = cols[i];
			table = getTable(col);
			if(table) {
				colRange = getColRange(col, cache);
				colsInfo.push({
					table: table,
					min: colRange.min,
					max: colRange.max
				});
			}
		}
		
		if(colsInfo.length == 0) return [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			tagName = el.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				table = getTable(el);
				if(table) {
					cellRange = false;
					for(var j = 0; j < colsInfo.length; j++) {
						colInfo = colsInfo[j];
						if(table == colInfo.table) {
							if(!cellRange) cellRange = getCellRange(el, cache);
							if(
								(cellRange.min >= colInfo.min && cellRange.min <= colInfo.max)
								|| (cellRange.max >= colInfo.min && cellRange.max <= colInfo.max)
								|| (cellRange.min <= colInfo.min && cellRange.max >= colInfo.max)
							) {
								newCurElements.push(el)
								break;
							}
						}
					}
				}
			}
		}
		
		return newCurElements;
		
	}
	
	function getTable(col) {
		var el = col;
		while(el = el.parentNode) {
			if(el.tagName == 'TABLE') return el;
		}
		return null;
	}
	
	function getColRange(el, cache) {
		
		var xel = el, colNum = 1, maxColNum, elId, cachedNum, tagName;
		
		while(xel = xel.previousSibling) {
			elId = xel._qs_elId;
			if(elId) cachedNum = cache[elId];
			if(cachedNum) {
				colNum += cachedNum;
				break;
			}
			tagName = xel.tagName;
			if(tagName == 'COL') {
				colNum += xel.span;
			}
		}
		
		maxColNum = colNum + el.span - 1;
		
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		// Cache the largest value in the range
		cache[elId] = maxColNum
		
		return {
			min: colNum,
			max: maxColNum
		};
		
	}
	
	function getCellRange(el, cache) {
		
		var xel = el, colNum = 1, maxColNum, elId, cachedNum, tagName;
		
		while(xel = xel.previousSibling) {
			elId = xel._qs_elId;
			if(elId) cachedNum = cache[elId];
			if(cachedNum) {
				colNum += cachedNum;
				break;
			}
			tagName = xel.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				colNum += xel.colSpan;
			}
		}
		
		maxColNum = colNum + el.colSpan - 1;
		
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		// Cache the largest value in the range
		cache[elId] = maxColNum
		
		return {
			min: colNum,
			max: maxColNum
		};
		
	}
		
	return filterColumn;
	
})();
var filterContains = (function() {
	
	function filterContains(content, curElements) {
		
		var el, newCurElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if((el.textContent || el.innerText || '').indexOf(content) > -1) {
				newCurElements.push(el);
			}
		}
		
		return newCurElements;
		
	}
	
	return filterContains;
	
})();
var filterCustom = (function() {
	
	function filterCustom(pseudoClass, argument, curElements) {
		
		var f = customPseudoClasses[pseudoClass],
			el, newCurElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(f(el, argument)) newCurElements.push(el);
		}
		
		return newCurElements;
		
	}
	
	return filterCustom;
	
})();
var filterDefault = (function() {
	// TODO: This currently checks for default checkboxes, radios, and submit buttons. Could there be another kind of default that should be returned?
	
	function filterDefault(curElements) {
		
		var el, newElements = [ ], type, cache = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el.defaultChecked) newElements.push(el);
			else if(el.tagName == 'INPUT' && el.type.toLowerCase() == 'submit') {
				// The first submit button in a form is a defacto default in most browsers.
				// TODO: Check this out in all target browsers to make, especially with variables
				// such as whether the buttons are hidden or whether they have strange tab indices
				// to see if this implementation needs to be altered.
				if(isFirstSubmitInForm(el, cache)) newElements.push(el);
			}
		}
		
		return newElements;
		
	}
	
	function isFirstSubmitInForm(submitEl, cache) {
		var formEl = submitEl, r, formElId;
		while(formEl = formEl.parentNode) {
			if(formEl.tagName == 'FORM') break;
		}
		if(!formEl) return false;
		formElId = formEl._qs_elId;
		if(!formElId) formElId = formEl._qs_elId = ++nextElId;
		if(cache[formElId]) return false;
		r = formEl.getElementsByTagName('input');
		for(var i = 0; i < r.length; i++) {
			if(r[i] == submitEl) {
				cache[formElId] = true;
				return true;
			} else if(r[i].type.toLowerCase() == 'submit') {
				cache[formElId] = true;
				return false;
			}
		}
	}
	
	return filterDefault;
	
})();
var filterDir = (function() {
	
	function filterDir(direction, curElements) {
		
		var el, newCurElements = [ ], cache = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(getDir(el, cache) == direction) newCurElements.push(el);
		}
		
		return newCurElements;
		
	}
	
	function getDir(el, cache) {
		var elId = el._qs_elId, elDir;
		if(!elId) elId = el._qs_elId = ++nextElId;
		else elDir = cache[elId];
		if(!elDir) {
			elDir = el.dir;
			while(!elDir) {
				el = el.parentNode;
				if(!el) break;;
				elDir = cache[el._qs_elId] || el.dir;
			}
		}
		cache[elId] = elDir;
		return elDir;
	}
	
	return filterDir;
	
})();
var filterDisabled = (function() {
	
	function filterDisabled(value, curElements) {
		
		var el, newElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			// style tags can have a disabled property.
			// TODO: Are there any other tags that can report a disabled property
			// but aren't user-interface elements?
			if(el.disabled === value && el.tagName != 'STYLE') newElements.push(el);
		}
		
		return newElements;
		
	}
	
	return filterDisabled;
	
})();
function filterEmpty(curElements) {
	
	var el, xel, newCurElements = [ ], isEmpty;
	
	for(var i = 0; i < curElements.length; i++) {
		el = curElements[i];
		isEmpty = true;
		xel = el.firstChild;
		if(xel) do {
			if(xel.nodeType < 6) { isEmpty = false; break; }
		} while(xel = xel.nextSibling);
		if(isEmpty) newCurElements.push(el);
	}
	
	return newCurElements;
	
}function filterFirstChild(curElements) {
	
	var el, cel, newCurElements = [ ], addEl;
	
	for(var i = 0; i < curElements.length; i++) {
		cel = el = curElements[i];
		addEl = true;
		// The root element should not be included; it has no parent.
		if(el == documentElement) addEl = false;
		else while(el = el.previousSibling) {
			if(el.nodeType == 1) {
				addEl = false;
				break;
			}
		}
		if(addEl) newCurElements.push(cel);
	}
	
	return newCurElements;
	
}
function filterFirstOfType(curElements) {
	
	var el, cel, newCurElements = [ ], addEl, tagName;
	
	for(var i = 0; i < curElements.length; i++) {
		cel = el = curElements[i];
		tagName = el.tagName;
		addEl = true;
		// The root element should not be included; it has no parent.
		if(el == documentElement) addEl = false;
		else while(el = el.previousSibling) {
			if(el.tagName == tagName) {
				addEl = false;
				break;
			}
		}
		if(addEl) newCurElements.push(cel);
	}
	
	return newCurElements;
	
}
var filterFocus = (function() {
	
	function filterFocus(curElements) {
		
		var el,
			activeEl;
		
		if(curElements.length == 0) return [ ];
		
		activeEl = curElements[0].ownerDocument.activeElement;
		if(!activeEl || !(activeEl.type || activeEl.href)) return [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el == activeEl) return [ el ];
		}
		
		return [ ];
		
	}
	
	return filterFocus;
	
})();
function filterIndeterminate(curElements) {
	
	var el, newElements = [ ];
	
	for(var i = 0; i < curElements.length; i++) {
		el = curElements[i];
		if(el.indeterminate) newElements.push(el);
	}
	
	return newElements;
	
}var filterLang = (function() {
	
	function filterLang(langs, curElements) {
		/* NOTE: According to the Selectors 4 Editor's Draft (http://dev.w3.org/csswg/selectors4/#lang-pseudo),
		 * languages should be matched based on RFC4647 (http://www.ietf.org/rfc/rfc4647.txt).
		 * This is a long document, and this implementation may need to be adjusted to correctly comply with it.
		 * This implementation is, instead, based on a mishmash of information in the Selector's Level 4
		 * Editor's Draft and the first Working Draft (http://www.w3.org/TR/selectors4/#lang-pseudo).
		 */
		
		var el, newCurElements = [ ], lang, cache = [ ], reLangs, reLangsStr;
		
		reLangsStr = '';
		for(var i = 0; i < langs.length; i++) {
			lang = langs[i];
			if(lang.substring(0, 2) == '*\\-') reLangStr += '^[a-z0-9]+' + genImplicitWildcards(langs[i].substring(2)) + '\\-?|';
			reLangsStr += '^' + genImplicitWildcards(langs[i]) + '\\-?|';
		}
		reLangs = new RegExp(reLangsStr.substring(0, reLangsStr.length - 1), 'i');
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(reLangs.test(getLang(el, cache))) newCurElements.push(el);
		}
		
		return newCurElements;
		
	}
	
	function getLang(el, cache) {
		var elId = el._qs_elId, elLang;
		if(!elId) elId = el._qs_elId = ++nextElId;
		else elLang = cache[elId];
		if(!elLang) {
			elLang = el.lang;
			while(!elLang) {
				el = el.parentNode;
				if(!el) break;
				elLang = cache[el._qs_elId] || el.lang;
			}
		}
		cache[elId] = elLang;
		return elLang;
	}
	
	function genImplicitWildcards(lang) {
		// From the examples in the Editor's Draft (http://dev.w3.org/csswg/selectors4/#lang-pseudo),
		// it seems like all dashes should be treated as possible implicit wildcards.
		// e.g. de-DE should match de-Latf-DE
		
		var parts = lang.split('-'), s = '';
		
		for(var i = 0; i < parts.length; i++) {
			s += parts[i];
			if(i < parts.length - 1) s += '\\-([a-z0-9]+\\-)*';
		}
		
		return s;
		
	}
	
	return filterLang;
	
})();function filterLastChild(curElements) {
	
	var el, cel, newCurElements = [ ], addEl;
	
	for(var i = 0; i < curElements.length; i++) {
		cel = el = curElements[i];
		addEl = true;
		// The root element should not be included; it has no parent.
		if(el == documentElement) addEl = false;
		else while(el = el.nextSibling) {
			if(el.nodeType == 1) {
				addEl = false;
				break;
			}
		}
		if(addEl) newCurElements.push(cel);
	}
	
	return newCurElements;
	
}
function filterLastOfType(curElements) {
	
	var el, cel, newCurElements = [ ], addEl, tagName;
	
	for(var i = 0; i < curElements.length; i++) {
		cel = el = curElements[i];
		tagName = el.tagName;
		addEl = true;
		// The root element should not be included; it has no parent.
		if(el == documentElement) addEl = false;
		else while(el = el.nextSibling) {
			if(el.tagName == tagName) {
				addEl = false;
				break;
			}
		}
		if(addEl) newCurElements.push(cel);
	}
	
	return newCurElements;
	
}
function filterNthChild(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element child number starting at 1
		elNum,
		
		// Cache child numbers
		cache = [ ], cachedNum,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ];
	
	for(var i = 0; i < curElements.length; i++) {
		
		cel = el = curElements[i];
		
		// The root element should not be included; it has no parent.
		if(el != documentElement) {
			
			elNum = 1;
			while(el = el.previousSibling) {
				if(el.nodeType == 1) {
					cachedNum = cache[el._qs_elId];
					if(cachedNum) {
						elNum += cachedNum;
						break;
					}
					elNum++;
				}
			}
			
			// Cache the element number for later elements in this loop
			elId = cel._qs_elId;
			if(!elId) elId = cel._qs_elId = ++nextElId;
			cache[elId] = elNum;
			
			// Add element if it fits the constraints
			if(a == 0) {
				if(elNum == b) newCurElements.push(cel);
			} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
				newCurElements.push(cel)
			}
			
		}
		
	}
	
	return newCurElements;
	
}
var filterNthColumn = (function() {
	
	function filterNthColumn(a, b, curElements) {
		
		var el, newCurElements = [ ], cache = [ ], colRange, tagName;
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			tagName = el.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				colRange = getColumnRange(el, cache);
				for(var colNum = colRange.min; colNum <= colRange.max; colNum++) {
					if(a == 0) {
						if(colNum == b) newCurElements.push(el);
					} else if(((colNum - b) % a) == 0 && colNum >= b && a * colNum + b >= 0) {
						newCurElements.push(el)
					}
				}
			}
		}
		
		return newCurElements;
		
	}
	
	function getColumnRange(el, cache) {
		
		var xel = el, colNum = 1, maxColNum, elId, cachedNum, tagName;
		
		while(xel = xel.previousSibling) {
			elId = xel._qs_elId;
			if(elId) cachedNum = cache[elId];
			if(cachedNum) {
				colNum += cachedNum;
				break;
			}
			tagName = xel.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				colNum += xel.colSpan;
			}
		}
		
		maxColNum = colNum + el.colSpan - 1;
		
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		// Cache the largest value in the range
		cache[elId] = maxColNum
		
		return {
			min: colNum,
			max: maxColNum
		};
		
	}
		
	return filterNthColumn;
	
})();
function filterNthLastChild(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element child number starting at 1
		elNum,
		
		// Cache child numbers
		cache = [ ], cachedNum,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ];
	
	for(var i = curElements.length - 1; i >= 0; i--) {
		
		cel = el = curElements[i];
		
		// The root element should not be included; it has no parent.
		if(el != documentElement) {
			
			elNum = 1;
			while(el = el.nextSibling) {
				if(el.nodeType == 1) {
					cachedNum = cache[el._qs_elId];
					if(cachedNum) {
						elNum += cachedNum;
						break;
					}
					elNum++;
				}
			}
			
			// Cache the element number for later elements in this loop
			elId = cel._qs_elId;
			if(!elId) elId = cel._qs_elId = ++nextElId;
			cache[elId] = elNum;
			
			// Add element if it fits the constraints
			if(a == 0) {
				if(elNum == b) newCurElements.push(cel);
			} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
				newCurElements.push(cel)
			}
			
		}
		
	}
	
	return newCurElements;
	
}
var filterNthLastColumn = (function() {
	
	function filterNthLastColumn(a, b, curElements) {
		
		var el, newCurElements = [ ], cache = [ ], colRange, tagName;
		
		for(var i = curElements.length - 1; i >= 0; i--) {
			el = curElements[i];
			tagName = el.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				colRange = getColumnRange(el, cache);
				for(var colNum = colRange.min; colNum <= colRange.max; colNum++) {
					if(a == 0) {
						if(colNum == b) newCurElements.push(el);
					} else if(((colNum - b) % a) == 0 && colNum >= b && a * colNum + b >= 0) {
						newCurElements.push(el)
					}
				}
			}
		}
		
		return newCurElements;
		
	}
	
	function getColumnRange(el, cache) {
		
		var xel = el, colNum = 1, maxColNum, elId, cachedNum, tagName;
		
		while(xel = xel.nextSibling) {
			elId = xel._qs_elId;
			if(elId) cachedNum = cache[elId];
			if(cachedNum) {
				colNum += cachedNum;
				break;
			}
			tagName = xel.tagName;
			if(tagName == 'TD' || tagName == 'TH') {
				colNum += xel.colSpan;
			}
		}
		
		maxColNum = colNum + el.colSpan - 1;
		
		elId = el._qs_elId;
		if(!elId) elId = el._qs_elId = ++nextElId;
		// Cache the largest value in the range
		cache[elId] = maxColNum
		
		return {
			min: colNum,
			max: maxColNum
		};
		
	}
	
	return filterNthLastColumn;
	
})();
function filterNthLastOfType(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element child number starting at 1
		elNum,
		
		// Cache child numbers
		cache = [ ], cachedNum,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ],
		
		tagName;
	
	for(var i = curElements.length - 1; i >= 0; i--) {
		
		cel = el = curElements[i];
		tagName = cel.tagName;
		
		// The root element should not be included; it has no parent.
		if(el != documentElement) {
			
			elNum = 1;
			while(el = el.nextSibling) {
				if(el.tagName == tagName) {
					cachedNum = cache[el._qs_elId];
					if(cachedNum) {
						elNum += cachedNum;
						break;
					}
					elNum++;
				}
			}
			
			// Cache the element number for later elements in this loop
			elId = cel._qs_elId;
			if(!elId) elId = cel._qs_elId = ++nextElId;
			cache[elId] = elNum;
			
			// Add element if it fits the constraints
			if(a == 0) {
				if(elNum == b) newCurElements.push(cel);
			} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
				newCurElements.push(cel)
			}
			
		}
		
	}
	
	return newCurElements;
	
}
function filterNthOfType(a, b, curElements) {
	
	var el, cel, elId,
		
		// The element child number starting at 1
		elNum,
		
		// Cache child numbers
		cache = [ ], cachedNum,
		
		// Using a new array to push to seems faster than splicing out the old ones in IE7
		newCurElements = [ ],
		
		tagName;
	
	for(var i = 0; i < curElements.length; i++) {
		
		cel = el = curElements[i];
		tagName = cel.tagName;
		
		// The root element should not be included; it has no parent.
		if(el != documentElement) {
			
			elNum = 1;
			while(el = el.previousSibling) {
				if(el.tagName == tagName) {
					cachedNum = cache[el._qs_elId];
					if(cachedNum) {
						elNum += cachedNum;
						break;
					}
					elNum++;
				}
			}
			
			// Cache the element number for later elements in this loop
			elId = cel._qs_elId;
			if(!elId) elId = cel._qs_elId = ++nextElId;
			cache[elId] = elNum;
			
			// Add element if it fits the constraints
			if(a == 0) {
				if(elNum == b) newCurElements.push(cel);
			} else if(((elNum - b) % a) == 0 && elNum >= b && a * elNum + b >= 0) {
				newCurElements.push(cel)
			}
			
		}
		
	}
	
	return newCurElements;
	
}
var filterOnlyChild = (function() {
	
	function filterOnlyChild(curElements) {
		
		var el, newCurElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el != documentElement && !hasNextElement(el) && !hasPreviousElement(el)) {
				newCurElements.push(el);
			}
		}
		
		return newCurElements;
		
	}
	
	function hasPreviousElement(el) {
		while(el = el.previousSibling) {
			if(el.nodeType == 1) return true;
		}
		return false;
	}
	
	function hasNextElement(el) {
		while(el = el.nextSibling) {
			if(el.nodeType == 1) return true;
		}
		return false;
	}
	
	return filterOnlyChild;
	
})();
var filterOnlyOfType = (function() {
	
	function filterOnlyOfType(curElements) {
		
		var el, newCurElements = [ ], tagName;
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			tagName = el.tagName;
			if(el != documentElement && !hasNextElement(el, tagName) && !hasPreviousElement(el, tagName)) {
				newCurElements.push(el);
			}
		}
		
		return newCurElements;
		
	}
	
	function hasPreviousElement(el, tagName) {
		while(el = el.previousSibling) {
			if(el.tagName == tagName) return true;
		}
		return false;
	}
	
	function hasNextElement(el, tagName) {
		while(el = el.nextSibling) {
			if(el.tagName == tagName) return true;
		}
		return false;
	}
	
	return filterOnlyOfType;
	
})();
var filterReadOnly = (function() {
	
	function filterReadOnly(readOnly, curElements) {
		// Selects input[type=text], textarea, and elements with contentEditable set to true.
		// TODO: Are there other elements that should be included?
		// TODO: Isn't there an old IE version of contentEditable under another name? Should that be included?
		
		var el, newCurElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(
				(el.tagName == 'INPUT' && el.type.toLowerCase() == 'text')
				|| el.tagName == 'TEXTAREA'
				|| isEditable(el)
			) {
				if(!readOnly) newCurElements.push(el);
			} else if(readOnly) newCurElements.push(el);
		}
		
		return newCurElements;
		
	}
	
	function isEditable(el) {
		while(el && el.contentEditable == 'inherit') {
			el = el.parentNode;
		}
		if(!el) return false;
		// TODO: Are these values correct?
		if(el.contentEditable == 'true' || el.contentEditable == true) return true;
		return false;
	}
	
	return filterReadOnly;
	
})();
var filterRequired = (function() {
	
	function filterRequired(value, curElements) {
		
		var el, newCurElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el.required === value) newCurElements.push(el);
		}
		
		return newCurElements;
		
	}
	
	return filterRequired;
	
})();
var filterRoot = (function() {
	
	function filterRoot(curElements) {
		
		var el;
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el == documentElement) return [ el ];
		}
		
		return [ ];
		
	}
	
	return filterRoot;
	
})();
function filterScope(curElements, scope) {
	
	if(!scope) return [ ];
	
	for(var i = 0; i < curElements.length; i++) {
		if(curElements[i] == scope) return [ scope ];
	}
	
	return [ ];
	
}var filterTarget = (function() {
	
	function filterTarget(curElements) {
		
		var el,
			fragId = location.hash,
			potentialEl;
		
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el.id == fragId) return [ el ];
			else if(!potentialEl && el.name == fragId) potentialEl = el;
		}
		
		if(potentialEl && potentialEl.tagName == 'A') return [ potentialEl ];
		else return [ ];
		
	}
	
	return filterTarget;
	
})();
var filterValid = (function() {
	
	function filterValid(value, curElements) {
		
		var el, newElements = [ ];
		
		for(var i = 0; i < curElements.length; i++) {
			el = curElements[i];
			if(el.validity && el.validity.valid === value) newElements.push(el);
		}
		
		return newElements;
		
	}
	
	return filterValid;
	
})();

	
	function filterPseudoClasses(pseudoClasses, algorithm) {
		
		var pc, f;
		
		for(var i = 0; i < pseudoClasses.length; i++) {
			pc = pseudoClasses[i];
			switch(pc.pseudoClass) {
				
				case FIRST_CHILD_PSEUDOCLASS:
					algorithm.push({
						call: filterFirstChild
					});
					break;
				case LAST_CHILD_PSEUDOCLASS:
					algorithm.push({
						call: filterLastChild
					});
					break;
				case FIRST_OF_TYPE_PSEUDOCLASS:
					algorithm.push({
						call: filterFirstOfType
					});
					break;
				case NTH_CHILD_PSEUDOCLASS:
					algorithm.push({
						call: filterNthChild,
						arguments: [ pc.a, pc.b ]
					});
					break;
				case NTH_LAST_CHILD_PSEUDOCLASS:
					algorithm.push({
						call: filterNthLastChild,
						arguments: [ pc.a, pc.b ]
					});
					break;
				case NTH_OF_TYPE_PSEUDOCLASS:
					algorithm.push({
						call: filterNthOfType,
						arguments: [ pc.a, pc.b ]
					});
					break;
				case NTH_LAST_OF_TYPE_PSEUDOCLASS:
					algorithm.push({
						call: filterNthLastOfType,
						arguments: [ pc.a, pc.b ]
					});
					break;
				case ONLY_CHILD_PSEUDOCLASS:
					algorithm.push({
						call: filterOnlyChild
					});
					break;
				case ONLY_OF_TYPE_PSEUDOCLASS:
					algorithm.push({
						call: filterOnlyOfType
					});
					break;
				
				case CONTAINS_PSEUDOCLASS:
					algorithm.push({
						call: filterContains,
						arguments: [ pc.content ]
					});
					break;
				case EMPTY_PSEUDOCLASS:
					algorithm.push({
						call: filterEmpty
					});
					break;
					
				case TARGET_PSEUDOCLASS:
					algorithm.push({
						call: filterTarget
					});
					break;
				case SCOPE_PSEUDOCLASS:
					algorithm.push({
						call: filterScope
					});
					break;
				
				case HOVER_PSEUDOCLASS: throw 'Quicksand: The :hover pseudo-class is not supported due to limitations in JavaScript and performance concerns.';
				case ACTIVE_PSEUDOCLASS: throw 'Quicksand: The :active pseudo-class is not supported due to limitations in JavaScript and performance concerns.';
				case FOCUS_PSEUDOCLASS:
					algorithm.push({
						call: filterFocus
					});
					break;
				
				case CURRENT_PSEUDOCLASS:
				case PAST_PSEUDOCLASS:
				case FUTURE_PSEUDOCLASS:
					throw 'Quicksand: Time-dimensional pseudo-classes (:current, :past, :future) are not supported.';
				
				case DIR_PSEUDOCLASS:
					algorithm.push({
						call: filterDir,
						arguments: [ pc.direction ]
					});
					break;
				case LANG_PSEUDOCLASS:
					algorithm.push({
						call: filterLang,
						arguments: [ pc.languages ]
					});
					break;
					
				case ENABLED_PSEUDOCLASS:
					algorithm.push({
						call: filterDisabled,
						arguments: [ false ]
					});
					break;
				case DISABLED_PSEUDOCLASS:
					algorithm.push({
						call: filterDisabled,
						arguments: [ true ]
					});
					break;
				case CHECKED_PSEUDOCLASS:
					algorithm.push({
						call: filterChecked,
						arguments: [ true ]
					});
					break;
				case UNCHECKED_PSEUDOCLASS:
					algorithm.push({
						call: filterChecked,
						arguments: [ false ]
					});
					break;
				case INDETERMINATE_PSEUDOCLASS:
					/* Note: Even though the indeterminate property is not supported by older target browsers,
					 * we can go ahead and support this property without a warning because any implementation
					 * which wants to select by :indeterminate will have to have already used the indeterminate
					 * property at some point. Therefore, support for indeterminate should have already been
					 * assessed by the script calling for the selection.
					 */
					algorithm.push({
						call: filterIndeterminate
					});
					break;
				case DEFAULT_PSEUDOCLASS:
					algorithm.push({
						call: filterDefault
					});
					break;
				case VALID_PSEUDOCLASS:
					// Note: The same note as on :indeterminate also applies to :valid and :invalid
					algorithm.push({
						call: filterValid,
						arguments: [ true ]
					});
					break;
				case INVALID_PSEUDOCLASS:
					algorithm.push({
						call: filterValid,
						arguments: [ false ]
					});
					break;
				case IN_RANGE_PSEUDOCLASS:
				case OUT_OF_RANGE_PSEUDOCLASS:
					// :in-range and :out-of-range will remain unsupported for now, due to a lack of
					// browser support for <input type="range" /> (at the moment, FF12 doesn't support),
					// and lack of understanding of when this selector would be used (Chrome supports
					// <input type="range" />, but it's unclear how it could get out of range; trying to
					// set it out of range with JavaScript fails).
					throw 'Quicksand: The :in-range and :out-of-range pseudoclasses are currently not supported.';
				case REQUIRED_PSEUDOCLASS:
					algorithm.push({
						call: filterRequired,
						arguments: [ true ]
					});
					break;
				case OPTIONAL_PSEUDOCLASS:
					algorithm.push({
						call: filterRequired,
						arguments: [ false ]
					});
					break;
				case READ_ONLY_PSEUDOCLASS:
					algorithm.push({
						call: filterReadOnly,
						arguments: [ true ]
					});
					break;
				case READ_WRITE_PSEUDOCLASS:
					algorithm.push({
						call: filterReadOnly,
						arguments: [ false ]
					});
					break;
					
				case ROOT_PSEUDOCLASS:
					algorithm.push({
						call: filterRoot
					});
					break;
				
				case COLUMN_PSEUDOCLASS:
					algorithm.push({
						call: filterColumn,
						arguments: [ pc.selector ]
					});
					break;
				case NTH_COLUMN_PSEUDOCLASS:
					algorithm.push({
						call: filterNthColumn,
						arguments: [ pc.a, pc.b ]
					});
					break;
				case NTH_LAST_COLUMN_PSEUDOCLASS:
					algorithm.push({
						call: filterNthLastColumn,
						arguments: [ pc.a, pc.b ]
					});
					break;
				
				case NTH_MATCH_PSEUDOCLASS:
				case NTH_LAST_MATCH_PSEUDOCLASS:
					/* There are a few reasons :nth-match and :nth-last-match are not supported including some ambiguity
					 * and lack of clarity in the working draft. It also seems like the kind of thing that could change
					 * dramatically as the spec is developed.
					 * Another major reason nth-match is not supported is it's current form seems cumbersome and confusing.
					 * Quicksand has :nth and :nth-last pseudo-classes which are thought to be more clear, less verbose,
					 * and more in the spirit of CSS (not sacrificing simplicity, understandability, and readability for power).
					 * The :nth-match and :nth-match-last selectors, as they stand, seem more like XPATH selectors (power rules).
					 */
					throw 'Quicksand: The :nth-match and :nth-last-match pseudoclasses are currently not supported.\nTry using Quicksand\'s :nth or :nth-last instead.';
				
				default:
					if(!customPseudoClasses[pc.pseudoClass]) throw 'Quicksand: Pseudo-class not implemented: ' + pc.pseudoClass;
					// The customPseudoClasses[pc.pseudoClass] function is not itself cached in order to allow it to be changed.
					algorithm.push({
						call: filterCustom,
						arguments: [ pc.pseudoClass, pc.argument ]
					});
					break;
				
			}
		}
		
	}
	
	return filterPseudoClasses;
	
})();// Optimized selection path for classes
var selectByPath_classes = (function() {
	
	var supportsGEBCN = !!documentElement.getElementsByClassName,
		selectDescendants = supportsGEBCN ? selectDescendantsGEBCN : selectDescendantsRegex,
		selectGeneralSiblings = supportsGEBCN ? selectGeneralSiblingsGEBCN : selectGeneralSiblingsRegex,
		selectChildren = supportsGEBCN ? selectChildrenGEBCN : selectChildrenRegex,
		selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_classes(item, algorithm) {
		
		var combinator = item.combinator,
			cSel = item.compoundSelector,
			classes = cSel.classes,
			className = classes.join(' '),
			regexes = cSel.classes_regexes,
			curElements = [ ];
		
		switch(combinator.type) {
			
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants,
					arguments: [ className, regexes ]
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings,
					arguments: [ regexes ]
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings,
					arguments: [ className, regexes ]
				});
				break;
				
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren,
					arguments: [ className, regexes ]
				});
				break;
				
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ combinator.attribute.name, className, regexes ]
				});
				break;
			
		}
		
	}
	
	function selectDescendantsGEBCN(className, regexes, p) {
		var curElements = [ ];
		for(var i = 0; i < p.length; i++) {
			fPush.apply(curElements, p[i].getElementsByClassName(className));
		}
		return curElements;
	}
	
	function selectDescendantsRegex(className, regexes, p) {
		var curElements = [ ], ch, el;
		for(var i = 0; i < p.length; i++) {
			ch = p[i].getElementsByTagName('*');
			for(var j = 0, chl = ch.length; j < chl; j++) {
				el = ch[j];
				if(hasClasses(el.className, regexes)) curElements.push(el);
			}
		}
		return curElements;
	}
	
	function selectAdjacentSiblings(regexes, p) {
		var curElements = [ ], el;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			while(el = el.nextSibling) {
				if(el.nodeType == 1) {
					if(hasClasses(el.className, regexes)) curElements.push(el);
					break;
				}
			}
		}
		return curElements;
	}
	
	function selectGeneralSiblingsGEBCN(className, regexes, p) {
		// Use a random number to determine whether an element's child nodes have been processed or not.
		// TODO: probably should switch this over to elId method
		var curElements = [ ],
			callId = Math.random(),
			el, pel, ch, el2;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			pel = el.parentNode;
			if(pel._qs_selClass_GSB != callId) {
				pel._qs_selClass_GSB = callId;
				ch = pel.getElementsByClassName(className);
				for(var j = 0, chl = ch.length; j < chl; j++) {
					el2 = ch[j];
					if(el2.parentNode == pel && isGeneralSibling(el, el2)) {
						curElements.push(el2);
						el = el2;
					}
				}
			}
		}
		return curElements;
	}
	
	function selectGeneralSiblingsRegex(className, regexes, p) {
		// Use a random number to determine whether an element's child nodes have been processed or not.
		var curElements = [ ],
			callId = Math.random(),
			el, pel;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			pel = el.parentNode;
			if(pel._qs_selClass_GSB != callId) {
				pel._qs_selClass_GSB = callId;
				while(el = el.nextSibling) {
					if(el.nodeType == 1 && hasClasses(el.className, regexes)) curElements.push(el);
				}
			}
		}
		return curElements;
	}
	
	function selectChildrenGEBCN(className, regexes, p) {
		var curElements = [ ], ch, pel;
		for(var i = 0; i < p.length; i++) {
			pel = p[i];
			ch = pel.getElementsByClassName(className);
			for(var j = 0, chl = ch.length; j < chl; j++) {
				el = ch[j];
				if(el.parentNode == pel) curElements.push(el);
			}
		}
		return curElements;
	}
	
	function selectChildrenRegex(className, regexes, p) {
		var curElements = [ ], el, pel;
		for(var i = 0; i < p.length; i++) {
			pel = p[i];
			el = pel.firstChild;
			do {
				if(el.nodeType == 1 && hasClasses(el.className, regexes)) curElements.push(el);
			} while(el = el.nextSibling);
		}
		return curElements;
	}
	
	function selectReferenceGA(attribute, className, regexes, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(!doc) doc = el.ownerDocument;
			cel = doc.getElementById(attrVal);
			if(cel && hasClasses(cel.className, regexes)) curElements.push(cel);
		}
		return curElements;
	}
	
	function selectReferenceA(attribute, className, regexes, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(!doc) doc = el.ownerDocument;
				cel = doc.getElementById(attrVal);
				if(cel && hasClasses(cel.className, regexes)) curElements.push(cel);
			}
		}
		return curElements;
	}
	
	return selectByPath_classes;
	
})();
// Optimized selection path for id
var selectByPath_id = (function() {
	
	var selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_id(item, algorithm) {
		// TODO: Filter out elements which don't match tagname or classes
		
		var id = item.compoundSelector.id;
		
		switch(item.combinator.type) {
			
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren,
					arguments: [ id ]
				});
				break;
				
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants,
					arguments: [ id ]
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings,
					arguments: [ id ]
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings,
					arguments: [ id ]
				});
				break;
			
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ item.combinator.attribute.name, id ]
				});
				break;
			
		}
		
	}
	
	function selectChildren(id, p) {
		var parent, el = document.getElementById(id);
		if(!el) return [ ];
		parent = el.parentNode;
		for(var i = 0; i < p.length; i++) {
			if(p[i] == parent) return [ el ];
		}
		return [ ];
	}
	
	function selectDescendants(id, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isAncestor(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function selectAdjacentSiblings(id, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isAdjacentSibling(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function selectGeneralSiblings(id, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isGeneralSibling(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function selectReferenceGA(attribute, id, p) {
		
		if(p.length == 0) return [ ];
		
		var doc = p[0].ownerDocument,
			potentialEl = doc.getElementById(id);
		if(!potentialEl) return [ ];
		
		var curElements = [ ], el, attrVal;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(attrVal == id) return [ potentialEl ];
		}
		return [ ];
		
	}
	
	function selectReferenceA(attribute, id, p) {
		
		if(p.length == 0) return [ ];
		
		var doc = p[0].ownerDocument,
			potentialEl = doc.getElementById(id);
		if(!potentialEl) return [ ];
		
		var curElements = [ ], el, attrVal;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(attrVal == id) return [ potentialEl ];
			}
		}
		return [ ];
		
	}
	
	return selectByPath_id;
	
})();
// Optimized selection path for id + tag or classes
var selectByPath_idPlus = (function() {
	
	var selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_idPlus(item, algorithm) {
		
		var cSel = item.compoundSelector,
			id = cSel.id,
			tagName = cSel.type.name == '*' ? false : cSel.type.name,
			classes_regexes = cSel.classes_regexes;
		
		switch(item.combinator.type) {
			
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren,
					arguments: [ id, tagName, classes_regexes ]
				});
				break;
				
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants,
					arguments: [ id, tagName, classes_regexes ]
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings,
					arguments: [ id, tagName, classes_regexes ]
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings,
					arguments: [ id, tagName, classes_regexes ]
				});
				break;
			
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ item.combinator.attribute.name, id, tagName, classes_regexes ]
				});
				break;
			
		}
		
	}
	
	function selectChildren(id, tagName, classes_regexes, p) {
		var parent, el = document.getElementById(id);
		if(!el) return [ ];
		if(tagName && el.tagName != tagName) return [ ];
		if(classes_regexes && !hasClasses(el, classes_regexes)) return [ ];
		parent = el.parentNode;
		for(var i = 0; i < p.length; i++) {
			if(p[i] == parent) return [ el ];
		}
		return [ ];
	}
	
	function selectDescendants(id, tagName, classes_regexes, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		if(tagName && el.tagName != tagName) return [ ];
		if(classes_regexes && !hasClasses(el, classes_regexes)) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isAncestor(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function selectAdjacentSiblings(id, tagName, classes_regexes, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		if(tagName && el.tagName != tagName) return [ ];
		if(classes_regexes && !hasClasses(el, classes_regexes)) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isAdjacentSibling(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function selectGeneralSiblings(id, tagName, classes_regexes, p) {
		var el = document.getElementById(id);
		if(!el) return [ ];
		if(tagName && el.tagName != tagName) return [ ];
		if(classes_regexes && !hasClasses(el, classes_regexes)) return [ ];
		for(var i = 0; i < p.length; i++) {
			if(isGeneralSibling(p[i], el)) return [ el ];
		}
		return [ ];
	}
	
	function isAdjacentSibling(elA, elB) {
		// Checks to see if elB is the element right after elA
		while(elA = elA.nextSibling) {
			if(elA.nodeType == 1) {
				if(elA == elB) return true;
				else return false;
			}
		}
		return false;
	}
	
	function selectReferenceGA(attribute, id, tagName, classes_regexes, p) {
		var el, attrVal, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(attrVal == id) {
				if(!doc) doc = el.ownerDocument;
				el = doc.getElementById(attrVal);
				if(el && el.tagName == tagName && hasClasses(el, classes_regexes)) return [ el ];
			}
		}
		return [ ];
	}
	
	function selectReferenceA(attribute, id, tagName, classes_regexes, p) {
		var el, attrVal, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(attrVal == id) {
					if(!doc) doc = el.ownerDocument;
					el = doc.getElementById(attrVal);
					if(el && el.tagName == tagName && hasClasses(el, classes_regexes)) return [ el ];
				}
			}
		}
		return [ ];
	}
	
	return selectByPath_idPlus;
	
})();
// Optimized selection path for tag name and classes
var selectByPath_tagAndClasses = (function() {
	
	var selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_tagAndClasses(item, algorithm) {
		
		var combinator = item.combinator,
			cSel = item.compoundSelector,
			tagName = cSel.type.name,
			regexes = cSel.classes_regexes;
		
		switch(combinator.type) {
			
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants,
					arguments: [ tagName, regexes ]
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings,
					arguments: [ tagName, regexes ]
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings,
					arguments: [ tagName, regexes ]
				});
				break;
				
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren,
					arguments: [ tagName, regexes ]
				});
				break;
			
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ combinator.attribute.name, tagName, regexes ]
				});
				break;
			
		}
		
	}
	
	function selectDescendants(tagName, regexes, p) {
		var curElements = [ ], ch, el;
		for(var i = 0; i < p.length; i++) {
			ch = p[i].getElementsByTagName(tagName);
			for(var j = 0, chl = ch.length; j < chl; j++) {
				el = ch[j];
				if(hasClasses(el.className, regexes)) curElements.push(el);
			}
		}
		return curElements;
	}
	
	function selectAdjacentSiblings(tagName, regexes, p) {
		var curElements = [ ], el;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			while(el = el.nextSibling) {
				if(el.nodeType == 1) {
					if(el.tagName == tagName && hasClasses(el.className, regexes)) curElements.push(el);
					break;
				}
			}
		}
		return curElements;
	}
	
	function selectGeneralSiblings(tagName, regexes, p) {
		var curElements = [ ], el, callId;
		// Use a random number to determine whether an element's child nodes have been processed or not.
		callId = Math.random();
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			if(el.parentNode._qs_selTag_GSB != callId) {
				el.parentNode._qs_selTag_GSB = callId;
				while(el = el.nextSibling) {
					if(el.nodeType == 1 && el.tagName == tagName && hasClasses(el.className, regexes)) curElements.push(el);
				}
			}
		}
		return curElements;
	}
	
	function selectChildren(tagName, regexes, p) {
		var curElements = [ ], el, pel, ch;
		for(var i = 0; i < p.length; i++) {
			pel = p[i];
			ch = pel.getElementsByTagName(tagName);
			for(var j = 0, chl = ch.length; j < chl; j++) {
				el = ch[j];
				if(el.parentNode == pel && hasClasses(el.className, regexes)) curElements.push(el);
			}
		}
		return curElements;
	}
	
	function selectReferenceGA(attribute, tagName, regexes, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(!doc) doc = el.ownerDocument;
			cel = doc.getElementById(attrVal);
			if(cel && cel.tagName == tagName && hasClasses(cel.className, regexes)) curElements.push(cel);
		}
		return curElements;
	}
	
	function selectReferenceA(attribute, tagName, regexes, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(!doc) doc = el.ownerDocument;
				cel = doc.getElementById(attrVal);
				if(cel && cel.tagName == tagName && hasClasses(cel.className, regexes)) curElements.push(cel);
			}
		}
		return curElements;
	}
	
	return selectByPath_tagAndClasses;
	
})();
// Optimized selection path for tag name
var selectByPath_tagName = (function() {
	
	var selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_tagName(item, algorithm) {
		
		var combinator = item.combinator,
			tagName = item.compoundSelector.type.name;
		
		switch(combinator.type) {
			
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants,
					arguments: [ tagName ]
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings,
					arguments: [ tagName ]
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings,
					arguments: [ tagName ]
				});
				break;
				
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren,
					arguments: [ tagName ]
				});
				break;
			
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ combinator.attribute.name, tagName ]
				});
				break;
			
		}
		
	}
	
	function selectDescendants(tagName, p) {
		// TODO: I think the following line is safe. Should it be uncommented and implemented elsewhere for improved performance?
		//if(p.length == 1) return p[0].getElementsByTagName(tagName);
		var curElements = [ ];
		for(var i = 0; i < p.length; i++) {
			fPush.apply(curElements, p[i].getElementsByTagName(tagName));
		}
		return curElements;
	}
	
	function selectAdjacentSiblings(tagName, p) {
		var curElements = [ ], el;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			while(el = el.nextSibling) {
				if(el.nodeType == 1) {
					if(el.tagName == tagName) curElements.push(el);
					break;
				}
			}
		}
		return curElements;
	}
	
	function selectGeneralSiblings(tagName, p) {
		// Use a random number to determine whether an element's child nodes have been processed or not.
		// TODO: It might be faster to switch from using callId to the element's qs ID.
		var curElements = [ ], el, callId;
		callId = Math.random();
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			if(el.parentNode._qs_selTag_GSB != callId) {
				el.parentNode._qs_selTag_GSB = callId;
				while(el = el.nextSibling) {
					if(el.nodeType == 1 && el.tagName == tagName) curElements.push(el);
				}
			}
		}
		return curElements;
	}
	
	function selectChildren(tagName, p) {
		var curElements = [ ], el, ch, pel;
		for(var i = 0; i < p.length; i++) {
			pel = p[i];
			ch = pel.getElementsByTagName(tagName);
			for(var j = 0, chl = ch.length; j < chl; j++) {
				el = ch[j];
				if(el.parentNode == pel) curElements.push(el);
			}
		}
		return curElements;
	}
	
	function selectReferenceGA(attribute, tagName, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(!doc) doc = el.ownerDocument;
			cel = doc.getElementById(attrVal);
			if(cel && cel.tagName == tagName) curElements.push(cel);
		}
		return curElements;
	}
	
	function selectReferenceA(attribute, tagName, p) {
		var curElements = [ ], el, attrVal, cel, doc;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(!doc) doc = el.ownerDocument;
				cel = doc.getElementById(attrVal);
				if(cel && cel.tagName == tagName) curElements.push(cel);
			}
		}
		return curElements;
	}
	
	return selectByPath_tagName;
	
})();
// Optimized selection path for :target pseudo-class
var selectByPath_target = (function() {
	
	var selectReference = supportsGetAttribute ? selectReferenceGA : selectReferenceA;
	
	function selectByPath_target(item, algorithm) {
		
		switch(item.combinator.type) {
			
			case CHILD_COMBINATOR:
				algorithm.push({
					call: selectChildren
				});
				break;
				
			case DESCENDANT_COMBINATOR:
				algorithm.push({
					call: selectDescendants
				});
				break;
				
			case ADJACENT_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectAdjacentSiblings
				});
				break;
				
			case GENERAL_SIBLING_COMBINATOR:
				algorithm.push({
					call: selectGeneralSiblings
				});
				break;
			
			case REFERENCE_COMBINATOR:
				algorithm.push({
					call: selectReference,
					arguments: [ item.combinator.attribute.name ]
				});
				break;
			
		}
		
	}
	
	function selectChildren(p) {
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var parent, el = document.getElementById(fragId);
		if(!el) {
			el = document.getElementsByName(fragId)[0];
			// Only count named elements if they are "a" elements (as per http://dev.w3.org/html5/spec/single-page.html#scroll-to-fragid)
			if(!el || el.tagName != 'A') return [ ];
		}
		parent = el.parentNode;
		for(var i = 0; i < p.length; i++) {
			if(p[i] == parent) return [ el ];
		}
		return [ ];
		
	}
	
	function selectDescendants(p) {
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var el = document.getElementById(fragId);
		if(!el) {
			el = document.getElementsByName(fragId)[0];
			// Only count named elements if they are "a" elements (as per http://dev.w3.org/html5/spec/single-page.html#scroll-to-fragid)
			if(!el || el.tagName != 'A') return [ ];
		}
		for(var i = 0; i < p.length; i++) {
			if(isAncestor(p[i], el)) return [ el ];
		}
		return [ ];
		
	}
	
	function selectAdjacentSiblings(p) {
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var el = document.getElementById(fragId);
		if(!el) {
			el = document.getElementsByName(fragId)[0];
			// Only count named elements if they are "a" elements (as per http://dev.w3.org/html5/spec/single-page.html#scroll-to-fragid)
			if(!el || el.tagName != 'A') return [ ];
		}
		for(var i = 0; i < p.length; i++) {
			if(isAdjacentSibling(p[i], el)) return [ el ];
		}
		return [ ];
		
	}
	
	function selectGeneralSiblings(p) {
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var el = document.getElementById(fragId);
		if(!el) {
			el = document.getElementsByName(fragId)[0];
			// Only count named elements if they are "a" elements (as per http://dev.w3.org/html5/spec/single-page.html#scroll-to-fragid)
			if(!el || el.tagName != 'A') return [ ];
		}
		for(var i = 0; i < p.length; i++) {
			if(isGeneralSibling(p[i], el)) return [ el ];
		}
		return [ ];
		
	}
	
	function selectReferenceGA(attribute, p) {
		
		if(p.length == 0) return [ ];
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var doc = p[0].ownerDocument,
			potentialEl = doc.getElementById(fragId);
		if(!potentialEl) return [ ];
		
		var curElements = [ ], el, attrVal;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.getAttribute(attribute, 2);
			if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
			if(attrVal == fragId) return [ potentialEl ];
		}
		return [ ];
		
	}
	
	function selectReferenceA(attribute, p) {
		
		if(p.length == 0) return [ ];
		
		var fragId = location.hash;
		if(!fragId) return [ ];
		else if(fragId.charAt(0) != '#') return [ ];
		fragId = fragId.substring(1);
		if(!fragId || fragId.charAt(0) == '!') return [ ];
		
		var doc = p[0].ownerDocument,
			potentialEl = doc.getElementById(fragId);
		if(!potentialEl) return [ ];
		
		var el, attrVal;
		for(var i = 0; i < p.length; i++) {
			el = p[i];
			attrVal = el.attributes[attribute];
			if(attrVal) {
				attrVal = attrVal.value;
				if(attrVal && attrVal.charAt(0) == '#') attrVal = attrVal.substring(1);
				if(attrVal == fragId) return [ potentialEl ];
			}
		}
		return [ ];
		
	}
	
	return selectByPath_target;
	
})();


	
	function processSelectorList(selectorList) {
		
		var selector, algorithm = [ ];
		
		for(var i = 0; i < selectorList.length; i++) {
			selector = selectorList[i];
			algorithm.push(processSelector(selector));
		}
		
		// Cache the algorithm on the selector list
		selectorList.algorithm = algorithm;
		
	}
	
	return processSelectorList;
	
})();

	var onready = (function() {
	// Note: This function is only intended to be used by setupSelect to make selector optimizations.
	// There is no guarantee that it will work on all browsers. If its use is expanded, it will need
	// to be modified to be sure the function will be called on all browsers.
	
	var callOnReady = [ ],
		ready = false,
		tm,
		
		reIsIe = /\sMSIE\s/,
		
		isIe = reIsIe.test(navigator.userAgent);
	
	function onready(f) {
		callOnReady.push(f);
	}
	
	function execReady() {
		if(ready) return;
		ready = true;
		for(var i = 0; i < callOnReady.length; i++) {
			callOnReady[i]();
		}
	}
	
	function checkIe() {
		if(ready) return;
		try { document.documentElement.doScroll('left'); }
		catch(x) { return; }
		clearInterval(tm);
	    execReady();
	}
	
	if(document.addEventListener) {
		document.addEventListener('DOMContentLoaded', execReady, false);
	} else if(isIe && window == top) {
		// IE8 should be the only browser that follows this path, since IE7 doesn't support
		// querySelectorAll and IE9 supports DOMContentLoaded
		tm = setInterval(checkIe, 250);
	} else {
		window.onload = execReady;
	}
	// No special path is needed for Opera and Safari since DOMContentLoaded and querySelectorAll
	// were both first supported in the same versions (3.1 and 9.0 respectively).
	
	// We are hesitant to use window.onload as a fallback, because we don't really want Quicksand
	// to touch that part of the DOM (even though it can be done while carefully preserving any existing functions).
	// We want to leave that area open for libraries & developers to use.
	// The fallback really shouldn't be needed, and in the rare event it is, it will be okay if
	// the browser misses out on some of the optimizations used in setupSelect (which is the only thing that
	// makes use of onload). The selector should work well and quickly without those optimizations.
	
	return onready;
	
})();

	// TODO: Cache useNativeCache using web storage when available.

var useStandardSelect,
	preProcessSelectorList,
	
select = (function() {
	
	var clockSelectors = [ ],
		clockSelectorsObj = {
			// selector: regex match for related selectors
			'body': /^body$/,
			'div': /^\w+$/,
			'body div': /^body\s+\w+$/,
			'div p': /^\w+\s+\w+$/,
			'div p a': /^[\w\s]+$/,
			'.class': /^\.[\w\-]+$/,
			'div.class': /^[\w\-]+\.[\w\-]+$/,
			'div.class1 p.class2': /^[\w\.\s\-]+$/,
			'p:nth-child(2n+1)': /\:nth\-/,
			'p:only-child': /\:only\-child/,
			'p:first-child': /\:first\-child/,
			'p:last-child': /\:last\-child/,
			'[attribute-start]': /(^|\s)\[.+\]/,
			'a[href]': /\[href\]/,
			'div[class]': /\[class\]/,
			'div[data-test]': /\[[\w\-]+\]/,
			'div[class=classname]': /\[class\=[\w\-]+\]/,
			'div[data-test=foo]': /\[\w+\=[\w\-]+\]/,
			'div[data-test^=foo]': /\[.+\]/,
			'div, p, a': /\,/,
			'div > p': /\>/,
			'p + .class': /\+/,
			'div ~ p': /\~/
		},
		
		// An array of regular expressions determining whether to use native querySelectorAll or standardSelect
		useNative = [ ],
		
		// A cache of whether to use native querySelectorAll or not for selectors
		useNativeCache = { },
		
		// Attemps to speed up selectors on Chrome have been mostly unsuccessful using advancedSelect.
		// Use a function specifically crafted for Chrome.
		reIsWebkit5Gt = /\sAppleWebKit\/[5-9]/,
		isWebkit5Gt = reIsWebkit5Gt.test(navigator.userAgent),
		reIsChrome = /\sChrome\//,
		isChrome = isWebkit5Gt && reIsChrome.test(navigator.userAgent),
		
		// The standardSelector has tested faster on Chrome 18 for these selectors
		reChromeUseStandard = /^body$|\:nth\-/,
		
		// A unique id to use in scoping querySelectorAll
		nativeSelectId = '_qs_ns_' + (new Date()).getTime();
	
	useStandardSelect = function() {
		select = standardSelect;
	};
	
	function standardSelect(selectorStr, root, scope) {
		// Quicksand's built-in selector, for when querySelectorAll is
		// not available, is too slow, or can't perform the selection
		
		if(!root) root = document;
		
		var selectorList = QuicksandParser.parse(selectorStr);
		
		preProcessSelectorList(selectorList);
				
		return qSelect(selectorList, root, scope);
		
	}
	
	preProcessSelectorList = function _preProcessSelectorList(selectorList) {
		// We don't need to optimize a selector twice -- the cached version will remain optimized
		if(!selectorList.optimized) {
			optimizeSelector(selectorList);
			if(!setupFastTracks(selectorList)) processSelectorList(selectorList);
			selectorList.optimized = true;
		}
	}
	
	function advancedSelect(selectorStr, root, scope) {
		// Choose between the built-in selector or querySelectorAll
		
		var cached = useNativeCache[selectorStr];
		
		if(cached === undefined) {
			for(var i = 0; i < useNative.length; i++) {
				if(useNative[i].regex.test(selectorStr)) {
					if(useNative[i].value) {
						useNativeCache[selectorStr] = true;
						try {
							return nativeSelect(selectorStr, root, scope);
						} catch(x) { break; }
					} else break;
				}
			}
			useNativeCache[selectorStr] = false;
			return standardSelect(selectorStr, root, scope);
		}
		else if(cached) return nativeSelect(selectorStr, root, scope);
		else return standardSelect(selectorStr, root, scope);
		
	}
	
	function nativeSelect(selectorStr, root, scope) {
		var selection = [ ], oldId, scopeId, list;
		if(root && root.nodeType != 9) {
			// Fix querySelectorAll to use the root element
			
			if(~selectorStr.indexOf(',')) {
				// Multiple selectors could be used, although the comma could be from a :not pseudo-class
				// or another pseudo-class or a string
				list = selectorStrToList(selectorStr);
				for(var i = 0; i < list.length; i++) {
					fPush.apply(selection, nativeSelect(list[i], root, scope));
				}
				return selection;
			}
			
			oldId = root.id;
			if(oldId) scopeId = oldId;
			else {
				scopeId = nativeSelectId;
				root.id = scopeId;
			}
			selectorStr = '[id="' + scopeId + '"] ' + selectorStr;
			
		}
		fPush.apply(selection, (scope || root || document).querySelectorAll(selectorStr));
		if(root) root.id = oldId;
		return selection;
	}
	
	function selectorStrToList(selectorStr) {
		// Can be used to convert a selector string which is a selector list
		// to an array of selector strings which aren't selector lists
		
		// Load places where the selector should be split
		var parensOpen = 0, inString = false, c, splitPositions = [ ], list = [ ], pos, lastPos;
		for(var i = 0; i < selectorStr.length; i++) {
			c = selectorStr.charAt(i);
			switch(c) {
				case '\\':
					// Skip the next character. Note: An advanced understanding of escape sequences is not needed
					// due to the fact that we are only looking for parentheses, quotes, and commas.
					// Longer escape sequences based on numbers will be ignored anyway.
					i++;
					break;
				case '"': case "'":
					if(!inString) inString = c;
					else if(inString == c) inString = false;
					break;
				case '(':
					parensOpen++;
					break;
				case ')':
					parensOpen--;
					break;
				case ',':
					if(!parensOpen && !inString) splitPositions.push(i);
					break;
			}
		}
		
		// now split at splitPositions
		lastPos = 0;
		for(var i = 0; i < splitPositions.length; i++) {
			pos = splitPositions[i];
			list.push(trim(selectorStr.substring(lastPos, pos)));
			lastPos = pos + 1;
		}
		list.push(trim(selectorStr.substring(lastPos)));
		
		return list;
		
	}
	
	function chromeSelect(selectorStr, root, scope) {
		var cached;
		cached = useNativeCache[selectorStr];
		if(cached === undefined) {
			if(reChromeUseStandard.test(selectorStr)) {
				useNativeCache[selectorStr] = false;
				return standardSelect(selectorStr, root, scope);
			} else {
				useNativeCache[selectorStr] = true;
				try {
					return nativeSelect(selectorStr, root, scope);
				} catch(x) {
					useNativeCache[selectorStr] = false;
					return standardSelect(selectorStr, root, scope);
				}
			}
		}
		else if(cached) return nativeSelect(selectorStr, root, scope);
		else return standardSelect(selectorStr, root, scope);
	}
	
	var currentSelector = 0;
	function setupAdvancedSelect() {
		for(var i in clockSelectorsObj) {
			if(clockSelectorsObj.hasOwnProperty(i)) {
				clockSelectors.push({
					selector: i,
					regex: clockSelectorsObj[i]
				});
			}
		}
		onready(function() {
			var selector;
			for(var i = 0; i < clockSelectors.length; i++) {
				selector = clockSelectors[i].selector;
				standardSelect(selector);
				try { document.querySelectorAll(selector); }
				catch(x) {
					useNativeCache[selector] = false;
				}
			}
			setTimeout(setupNextSelector, 100);
		});
	}
	function setupNextSelector() {
		// Check to see whether standardSelect or querySelectorAll is faster for a range of selectors for this browser on this page
		// TODO: Use WebWorkers when possible.
		
		var selector, regex,
			res, start, stop, qsaSpeed, stdSpeed,
			iterations, maxIterations = 100, maxTime = 50, r;
		
		do {
			selector = clockSelectors[currentSelector].selector;
			regex = clockSelectors[currentSelector].regex;
			currentSelector++;
			if(!selector) return;
		} while(useNativeCache[selector] !== undefined);
		
		iterations = 0;
		start = new Date().getTime();
		stop = start;
		while(iterations < maxIterations && stop - start < maxTime) {
			r = [ ];
			res = document.querySelectorAll(selector);
			fPush.apply(r, res);
			iterations++;
			stop = new Date().getTime();
		}
		qsaSpeed = (stop - start) / iterations;
		
		iterations = 0;
		start = new Date().getTime();
		stop = start;
		while(iterations < maxIterations && stop - start < maxTime) {
			res = standardSelect(selector);
			iterations++;
			stop = new Date().getTime();
		}
		stdSpeed = (stop - start) / iterations;
		
		if(qsaSpeed < stdSpeed) {
			// Faster on native querySelectorAll
			useNative.push({
				regex: regex,
				value: true
			});
		} else {
			// Faster on standardSelect
			useNative.push({
				regex: regex,
				value: false
			});
		}
		
		if(currentSelector < clockSelectors.length) setTimeout(setupNextSelector, 50);
		
	}
	
	if(document.querySelectorAll) {
		if(isChrome) return chromeSelect;
		else {
			setupAdvancedSelect();
			return advancedSelect;
		}
	} else return standardSelect;
	
})();
	
	// Library Object Definition
	var Quicksand = {
		
		// Debug Mode can be used to detect warnings in the console. If warn() is called, it will
		// only output to the console if debugMode is turned on.
		debugMode: false,
		
		version: {
			major: 2,
			minor: 1,
			revision: 2,
			beta: true
		},
		
		// Allow external access to the parser
		parser: QuicksandParser,
		
		select: select,
		
		useStandardSelect: function() {
			// Remap the select method to the Quicksand's own standardSelect method.
			// Disables use of querySelectorAll (mostly intended for debugging)
			useStandardSelect();
			Quicksand.select = select;
		},
		
		enableCss4: function() { return QuicksandParser.enableCss4.apply(QuicksandParser, arguments); },
		disableCss4: function() { return QuicksandParser.disableCss4.apply(QuicksandParser, arguments); },
		
		enableExtended: function() { return QuicksandParser.enableExtended.apply(QuicksandParser, arguments); },
		disableExtended: function() { return QuicksandParser.disableExtended.apply(QuicksandParser, arguments); },
		
		enableExperimental: function() { QuicksandParser.enableExperimental.apply(QuicksandParser, arguments); },
		disableExperimental: function() { QuicksandParser.disableExperimental.apply(QuicksandParser, arguments); },
		
		enableSubject: function() { QuicksandParser.enableSubject.apply(QuicksandParser, arguments); },
		disableSubject: function() { QuicksandParser.disableSubject.apply(QuicksandParser, arguments); },
		
		enableInitialCombinators: function() { QuicksandParser.allowInitialCombinator = true; },
		enableTerminalCombinators: function() { QuicksandParser.allowTerminalCombinator = true; },
		
		setCustomPseudoClass: function(identifier, f, options) {
			customPseudoClasses[QuicksandParser.addPseudoClass(identifier, options)] = f;
		},
		
		hasCustomPseudoClass: function(identifier) {
			var pcId = QuicksandParser.getPseudoClass(identifier);
			return !!pcId && !!customPseudoClasses[pcId];
		}
		
	};
	
	function trim(s) {
		if(s.trim) return s.trim();
		return s.replace(/^\s\s*/, '').replace(/\s\s*$/, '');
	}
	
	return Quicksand;
	
})();
















