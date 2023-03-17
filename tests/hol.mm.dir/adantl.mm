include "adantr.mm"
include "ancoms.mm"

theorem adantl
  let tr: term R
  let ts: term S
  let tt: term T
  assume adantr.1: |- R |= T
  assume adantr.2: |- S : bool


  assert |- ( S , R ) |= T

  proof
    tr
    ts
    tt
    tr
    ts
    tt
    adantr.1
    adantr.2
    adantr
    ancoms
end
