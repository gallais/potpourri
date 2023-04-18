function notEq($0,$1) {
    return (!($0 === $1)); }
function choose($0) {
    if ($0) {return {tag: 0};} else {return {tag: 1};};
}
function view($th) {
  switch($th.bigEnd) {
  // empty thinning, use Done
  case 0n: return {tag: 0};
  default: {
   // bigEnd is (S predBE)
   const $predBE = ($th.bigEnd-1n);
   // Test whether the bit at index 0 of encoding is 0
   const $bitTest = choose(notEq($th.encoding&1n, 0n));
   switch($bitTest.tag) {
     case 0: { // The test was true, use Keep
         const $tail = $th.encoding>>1n;
         return {tag: 1, val: {bigEnd: $predBE, encoding: $tail}}; }
     case 1: { // The test was false, use Drop
         const $tail = $th.encoding>>1n;
         return {tag: 2, val: {bigEnd: $predBE, encoding: $tail}}; }
}}}}

console.log((0n&1n) == 0n);
console.log(view({bigEnd: 4n, encoding: 9n}));
console.log(view({bigEnd: 4n, encoding: 8n}));
console.log(view({bigEnd: 5n, encoding: 13n}));

/*
    yntaxError: Identifier '$tail' has already been declared
    at wrapSafe (internal/modules/cjs/loader.js:915:16)
    at Module._compile (internal/modules/cjs/loader.js:963:27)
    at Object.Module._extensions..js (internal/modules/cjs/loader.js:1027:10)
    at Module.load (internal/modules/cjs/loader.js:863:32)
    at Function.Module._load (internal/modules/cjs/loader.js:708:14)
    at Function.executeUserEntryPoint [as runMain] (internal/modules/run_main.js:60:12)
    at internal/main/run_main_module.js:17:47
*/
