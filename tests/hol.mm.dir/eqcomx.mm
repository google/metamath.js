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
  step 2) kc(0,1): term ( = A )
  step 3) ta(): term A
  step 4) kc(2,3): term ( ( = A ) A )
  step 5) ke(): term =
  step 6) tb(): term B
  step 7) kc(5,6): term ( = B )
  step 8) ta(): term A
  step 9) kc(7,8): term ( ( = B ) A )
  step 10) tr(): term R
  step 11) ke(): term =
  step 12) ta(): term A
  step 13) kc(11,12): term ( = A )
  step 14) ta(): term A
  step 15) kc(13,14): term ( ( = A ) A )
  step 16) tr(): term R
  step 17) ke(): term =
  step 18) ta(): term A
  step 19) kc(17,18): term ( = A )
  step 20) tb(): term B
  step 21) kc(19,20): term ( ( = A ) B )
  step 22) tr(): term R
  step 23) eqcomx.3(): |- R,|=,(,(,=,A,),B,)
  step 24) ax-cb1(21,22,23): |- R : bool
  step 25) hal(): type al
  step 26) ta(): term A
  step 27) eqcomx.1(): |- A,:,al
  step 28) ax-refl(25,26,27): |- T. |= ( ( = A ) A )
  step 29) a1i(15,16,24,28): |- R |= ( ( = A ) A )
  step 30) ke(): term =
  step 31) ke(): term =
  step 32) ta(): term A
  step 33) kc(31,32): term ( = A )
  step 34) ta(): term A
  step 35) kc(33,34): term ( ( = A ) A )
  step 36) kc(30,35): term ( = ( ( = A ) A ) )
  step 37) ke(): term =
  step 38) tb(): term B
  step 39) kc(37,38): term ( = B )
  step 40) ta(): term A
  step 41) kc(39,40): term ( ( = B ) A )
  step 42) kc(36,41): term ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 43) tr(): term R
  step 44) ke(): term =
  step 45) ke(): term =
  step 46) ta(): term A
  step 47) kc(45,46): term ( = A )
  step 48) kc(44,47): term ( = ( = A ) )
  step 49) ke(): term =
  step 50) tb(): term B
  step 51) kc(49,50): term ( = B )
  step 52) kc(48,51): term ( ( = ( = A ) ) ( = B ) )
  step 53) ke(): term =
  step 54) ta(): term A
  step 55) kc(53,54): term ( = A )
  step 56) ta(): term A
  step 57) kc(55,56): term ( ( = A ) A )
  step 58) ke(): term =
  step 59) ke(): term =
  step 60) ta(): term A
  step 61) kc(59,60): term ( = A )
  step 62) kc(58,61): term ( = ( = A ) )
  step 63) ke(): term =
  step 64) tb(): term B
  step 65) kc(63,64): term ( = B )
  step 66) kc(62,65): term ( ( = ( = A ) ) ( = B ) )
  step 67) tr(): term R
  step 68) ke(): term =
  step 69) ke(): term =
  step 70) kc(68,69): term ( = = )
  step 71) ke(): term =
  step 72) kc(70,71): term ( ( = = ) = )
  step 73) ke(): term =
  step 74) ta(): term A
  step 75) kc(73,74): term ( = A )
  step 76) tb(): term B
  step 77) kc(75,76): term ( ( = A ) B )
  step 78) ke(): term =
  step 79) ke(): term =
  step 80) kc(78,79): term ( = = )
  step 81) ke(): term =
  step 82) kc(80,81): term ( ( = = ) = )
  step 83) tr(): term R
  step 84) ke(): term =
  step 85) ta(): term A
  step 86) kc(84,85): term ( = A )
  step 87) tb(): term B
  step 88) kc(86,87): term ( ( = A ) B )
  step 89) tr(): term R
  step 90) eqcomx.3(): |- R,|=,(,(,=,A,),B,)
  step 91) ax-cb1(88,89,90): |- R : bool
  step 92) hal(): type al
  step 93) hal(): type al
  step 94) hb(): type bool
  step 95) ht(93,94): type ( al -> bool )
  step 96) ht(92,95): type ( al -> ( al -> bool ) )
  step 97) ke(): term =
  step 98) hal(): type al
  step 99) weq(98): |- = : ( al -> ( al -> bool ) )
  step 100) ax-refl(96,97,99): |- T. |= ( ( = = ) = )
  step 101) a1i(82,83,91,100): |- R |= ( ( = = ) = )
  step 102) eqcomx.3(): |- R,|=,(,(,=,A,),B,)
  step 103) hal(): type al
  step 104) hal(): type al
  step 105) hb(): type bool
  step 106) ht(104,105): type ( al -> bool )
  step 107) ta(): term A
  step 108) tb(): term B
  step 109) ke(): term =
  step 110) ke(): term =
  step 111) hal(): type al
  step 112) weq(111): |- = : ( al -> ( al -> bool ) )
  step 113) hal(): type al
  step 114) weq(113): |- = : ( al -> ( al -> bool ) )
  step 115) eqcomx.1(): |- A,:,al
  step 116) eqcomx.2(): |- B,:,al
  step 117) ax-ceq(103,106,107,108,109,110,112,114,115,116): |- ( ( ( = = ) = ) , ( ( = A ) B ) ) |= ( ( = ( = A ) ) ( = B ) )
  step 118) syl2anc(66,67,72,77,101,102,117): |- R |= ( ( = ( = A ) ) ( = B ) )
  step 119) ke(): term =
  step 120) ta(): term A
  step 121) kc(119,120): term ( = A )
  step 122) ta(): term A
  step 123) kc(121,122): term ( ( = A ) A )
  step 124) tr(): term R
  step 125) ke(): term =
  step 126) ta(): term A
  step 127) kc(125,126): term ( = A )
  step 128) tb(): term B
  step 129) kc(127,128): term ( ( = A ) B )
  step 130) tr(): term R
  step 131) eqcomx.3(): |- R,|=,(,(,=,A,),B,)
  step 132) ax-cb1(129,130,131): |- R : bool
  step 133) hal(): type al
  step 134) ta(): term A
  step 135) eqcomx.1(): |- A,:,al
  step 136) ax-refl(133,134,135): |- T. |= ( ( = A ) A )
  step 137) a1i(123,124,132,136): |- R |= ( ( = A ) A )
  step 138) hal(): type al
  step 139) hb(): type bool
  step 140) ta(): term A
  step 141) ta(): term A
  step 142) ke(): term =
  step 143) ta(): term A
  step 144) kc(142,143): term ( = A )
  step 145) ke(): term =
  step 146) tb(): term B
  step 147) kc(145,146): term ( = B )
  step 148) hal(): type al
  step 149) hal(): type al
  step 150) hb(): type bool
  step 151) ht(149,150): type ( al -> bool )
  step 152) ke(): term =
  step 153) ta(): term A
  step 154) hal(): type al
  step 155) weq(154): |- = : ( al -> ( al -> bool ) )
  step 156) eqcomx.1(): |- A,:,al
  step 157) wc(148,151,152,153,155,156): |- ( = A ) : ( al -> bool )
  step 158) hal(): type al
  step 159) hal(): type al
  step 160) hb(): type bool
  step 161) ht(159,160): type ( al -> bool )
  step 162) ke(): term =
  step 163) tb(): term B
  step 164) hal(): type al
  step 165) weq(164): |- = : ( al -> ( al -> bool ) )
  step 166) eqcomx.2(): |- B,:,al
  step 167) wc(158,161,162,163,165,166): |- ( = B ) : ( al -> bool )
  step 168) eqcomx.1(): |- A,:,al
  step 169) eqcomx.1(): |- A,:,al
  step 170) ax-ceq(138,139,140,141,144,147,157,167,168,169): |- ( ( ( = ( = A ) ) ( = B ) ) , ( ( = A ) A ) ) |= ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 171) syl2anc(42,43,52,57,118,137,170): |- R |= ( ( = ( ( = A ) A ) ) ( ( = B ) A ) )
  step 172) ax-eqmp(4,9,10,29,171): |- R |= ( ( = B ) A )
end
