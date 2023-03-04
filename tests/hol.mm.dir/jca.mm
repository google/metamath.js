include "ax-jca.mm"

theorem jca
  let tr: term R
  let ts: term S
  let tt: term T
  assume ax-jca.1: |- R |= S
  assume ax-jca.2: |- R |= T


  assert |- R |= ( S , T )

  step 0) tr(): term R
  step 1) ts(): term S
  step 2) tt(): term T
  step 3) ax-jca.1(): |- R,|=,S
  step 4) ax-jca.2(): |- R,|=,T
  step 5) ax-jca(0,1,2,3,4): |- R |= ( S , T )
end
