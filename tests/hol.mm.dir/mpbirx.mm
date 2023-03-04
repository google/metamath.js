include "hb.mm"
include "ax-cb2.mm"
include "eqcomx.mm"
include "ax-eqmp.mm"

theorem mpbirx
  let ta: term A
  let tb: term B
  let tr: term R
  assume mpbirx.1: |- B : bool
  assume mpbirx.2: |- R |= A
  assume mpbirx.3: |- R |= ( ( = B ) A )


  assert |- R |= B

  step 0) ta(): term A
  step 1) tb(): term B
  step 2) tr(): term R
  step 3) mpbirx.2(): |- R,|=,A
  step 4) hb(): type bool
  step 5) tb(): term B
  step 6) ta(): term A
  step 7) tr(): term R
  step 8) mpbirx.1(): |- B,:,bool
  step 9) ta(): term A
  step 10) tr(): term R
  step 11) mpbirx.2(): |- R,|=,A
  step 12) ax-cb2(9,10,11): |- A : bool
  step 13) mpbirx.3(): |- R,|=,(,(,=,B,),A,)
  step 14) eqcomx(4,5,6,7,8,12,13): |- R |= ( ( = A ) B )
  step 15) ax-eqmp(0,1,2,3,14): |- R |= B
end
