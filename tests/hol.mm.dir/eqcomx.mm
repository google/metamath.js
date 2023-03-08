include "ke.mm"
include "kc.mm"
include "ax-cb1.mm"
include "ax-refl.mm"
include "a1i.mm"
include "hb.mm"
include "ht.mm"
include "weq.mm"
include "ax-ceq.mm"
include "syl2anc.mm"
include "wc.mm"
include "ax-eqmp.mm"

theorem eqcomx
  let hal: type al
  let ta: term A
  let tb: term B
  let tr: term R
  assume eqcomx.1: |- A : al
  assume eqcomx.2: |- B : al
  assume eqcomx.3: |- R |= ( ( = A ) B )


  assert |- R |= ( ( = B ) A )

  step 0) ke(): term =
  step 1) ta(): term A
  step 2) kc(0, 1): term ( = A )
  step 3) #: term ( = A )
  step 4) ta(): term A
  step 5) kc(2, 3): term ( ( = A ) A )
  step 6) #: term ( ( = A ) A )
  step 7) ke(): term =
  step 8) tb(): term B
  step 9) kc(5, 6): term ( = B )
  step 10) #: term ( = B )
  step 11) ta(): term A
  step 12) kc(7, 8): term ( ( = B ) A )
  step 13) #: term ( ( = B ) A )
  step 14) tr(): term R
  step 15) @1: term ( ( = A ) A )
  step 16) tr(): term R
  step 17) @0: term ( = A )
  step 18) tb(): term B
  step 19) kc(2, 12): term ( ( = A ) B )
  step 20) #: term ( ( = A ) B )
  step 21) tr(): term R
  step 22) eqcomx.3(): |- R |= ( ( = A ) B )
  step 23) ax-cb1(13, 14, 15): |- R : bool
  step 24) #: |- R : bool
  step 25) hal(): type al
  step 26) ta(): term A
  step 27) eqcomx.1(): |- A : al
  step 28) ax-refl(17, 18, 19): |- T. |= ( ( = A ) A )
  step 29) a1i(4, 11, 16, 20): |- R |= ( ( = A ) A )
  step 30) #: |- R |= ( ( = A ) A )
  step 31) ke(): term =
  step 32) @1: term ( ( = A ) A )
  step 33) kc(22, 4): term ( = ( ( = A ) A ) )
  step 34) @3: term ( ( = B ) A )
  step 35) kc(23, 9): term ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 36) tr(): term R
  step 37) ke(): term =
  step 38) @0: term ( = A )
  step 39) kc(26, 2): term ( = ( = A ) )
  step 40) @2: term ( = B )
  step 41) kc(27, 7): term ( ( = ( = A ) ) ( = B ) )
  step 42) #: term ( ( = ( = A ) ) ( = B ) )
  step 43) @1: term ( ( = A ) A )
  step 44) @7: term ( ( = ( = A ) ) ( = B ) )
  step 45) tr(): term R
  step 46) ke(): term =
  step 47) ke(): term =
  step 48) kc(30, 31): term ( = = )
  step 49) ke(): term =
  step 50) kc(32, 33): term ( ( = = ) = )
  step 51) #: term ( ( = = ) = )
  step 52) @4: term ( ( = A ) B )
  step 53) @8: term ( ( = = ) = )
  step 54) tr(): term R
  step 55) @5: |- R : bool
  step 56) hal(): type al
  step 57) hal(): type al
  step 58) hb(): type bool
  step 59) ht(37, 38): type ( al -> bool )
  step 60) #: type ( al -> bool )
  step 61) ht(36, 39): type ( al -> ( al -> bool ) )
  step 62) ke(): term =
  step 63) hal(): type al
  step 64) weq(42): |- = : ( al -> ( al -> bool ) )
  step 65) #: |- = : ( al -> ( al -> bool ) )
  step 66) ax-refl(40, 41, 43): |- T. |= ( ( = = ) = )
  step 67) a1i(34, 35, 16, 44): |- R |= ( ( = = ) = )
  step 68) eqcomx.3(): |- R |= ( ( = A ) B )
  step 69) hal(): type al
  step 70) @9: type ( al -> bool )
  step 71) ta(): term A
  step 72) tb(): term B
  step 73) ke(): term =
  step 74) ke(): term =
  step 75) @10: |- = : ( al -> ( al -> bool ) )
  step 76) @10: |- = : ( al -> ( al -> bool ) )
  step 77) eqcomx.1(): |- A : al
  step 78) eqcomx.2(): |- B : al
  step 79) ax-ceq(47, 39, 48, 49, 50, 51, 43, 43, 52, 53): |- ( ( ( = = ) = ) , ( ( = A ) B ) ) |= ( ( = ( = A ) ) ( = B ) )
  step 80) syl2anc(28, 29, 34, 13, 45, 46, 54): |- R |= ( ( = ( = A ) ) ( = B ) )
  step 81) @6: |- R |= ( ( = A ) A )
  step 82) hal(): type al
  step 83) hb(): type bool
  step 84) ta(): term A
  step 85) ta(): term A
  step 86) @0: term ( = A )
  step 87) @2: term ( = B )
  step 88) hal(): type al
  step 89) @9: type ( al -> bool )
  step 90) ke(): term =
  step 91) ta(): term A
  step 92) @10: |- = : ( al -> ( al -> bool ) )
  step 93) eqcomx.1(): |- A : al
  step 94) wc(60, 39, 61, 62, 43, 63): |- ( = A ) : ( al -> bool )
  step 95) hal(): type al
  step 96) @9: type ( al -> bool )
  step 97) ke(): term =
  step 98) tb(): term B
  step 99) @10: |- = : ( al -> ( al -> bool ) )
  step 100) eqcomx.2(): |- B : al
  step 101) wc(65, 39, 66, 67, 43, 68): |- ( = B ) : ( al -> bool )
  step 102) eqcomx.1(): |- A : al
  step 103) eqcomx.1(): |- A : al
  step 104) ax-ceq(56, 57, 58, 59, 2, 7, 64, 69, 70, 71): |- ( ( ( = ( = A ) ) ( = B ) ) , ( ( = A ) A ) ) |= ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 105) syl2anc(24, 25, 28, 4, 55, 21, 72): |- R |= ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 106) ax-eqmp(4, 9, 10, 21, 73): |- R |= ( ( = B ) A )
end
