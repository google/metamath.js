include "kct.mm"
include "ax-cb1.mm"
include "simpl.mm"
include "syl.mm"

theorem adantr
  let tr: term R
  let ts: term S
  let tt: term T
  assume adantr.1: |- R |= T
  assume adantr.2: |- S : bool


  assert |- ( R , S ) |= T

  proof
    tr
    ts
    kct
    tr
    tt
    tr
    ts
    tt
    tr
    adantr.1
    ax-cb1
    adantr.2
    simpl
    adantr.1
    syl
end
