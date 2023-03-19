include "ctgp.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctmd.mm"
include "ccn.mm"
include "co.mm"
include "istgp.mm"
include "simp3bi.mm"

theorem tgpinv
  let cG: class G
  let cI: class I
  let cJ: class J
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgpinv.5: |- I = ( invg ` G )


  assert |- ( G e. TopGrp -> I e. ( J Cn J ) )

  proof
    cG
    ctgp
    wcel
    cG
    cgrp
    wcel
    cG
    ctmd
    wcel
    cI
    cJ
    cJ
    ccn
    co
    wcel
    cG
    cI
    cJ
    tgpcn.j
    tgpinv.5
    istgp
    simp3bi
end
