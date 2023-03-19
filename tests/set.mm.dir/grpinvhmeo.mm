include "ctgp.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "ccnv.mm"
include "chmeo.mm"
include "tgpinv.mm"
include "cgrp.mm"
include "wceq.mm"
include "tgpgrp.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "grpinvcnv.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem grpinvhmeo
  let cG: class G
  let cI: class I
  let cJ: class J
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgpinv.5: |- I = ( invg ` G )


  assert |- ( G e. TopGrp -> I e. ( J Homeo J ) )

  proof
    cG
    ctgp
    wcel
    #
    cI
    cJ
    cJ
    ccn
    co
    #
    wcel
    cI
    ccnv
    #
    @1
    wcel
    cI
    cJ
    cJ
    chmeo
    co
    wcel
    cG
    cI
    cJ
    tgpcn.j
    tgpinv.5
    tgpinv
    #
    @0
    @2
    cI
    @1
    @0
    cG
    cgrp
    wcel
    @2
    cI
    wceq
    cG
    tgpgrp
    cG
    cbs
    cfv
    #
    cG
    cI
    @4
    eqid
    tgpinv.5
    grpinvcnv
    syl
    @3
    eqeltrd
    cI
    cJ
    cJ
    ishmeo
    sylanbrc
end
