include "ctgp.mm"
include "wcel.mm"
include "cha.mm"
include "ct1.mm"
include "haust1.mm"
include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "ccld.mm"
include "cuni.mm"
include "wi.mm"
include "cbs.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "ctopon.mm"
include "wceq.mm"
include "tgptopon.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "t1sncld.mm"
include "expcom.mm"
include "tgphaus.mm"
include "sylibrd.mm"
include "impbid2.mm"

theorem tgpt1
  let cG: class G
  let cJ: class J
  assume tgpt1.j: |- J = ( TopOpen ` G )


  assert |- ( G e. TopGrp -> ( J e. Haus <-> J e. Fre ) )

  proof
    cG
    ctgp
    wcel
    #
    cJ
    cha
    wcel
    #
    cJ
    ct1
    wcel
    #
    cJ
    haust1
    @0
    @2
    cG
    c0g
    cfv
    #
    csn
    cJ
    ccld
    cfv
    wcel
    #
    @1
    @0
    @3
    cJ
    cuni
    #
    wcel
    #
    @2
    @4
    wi
    @0
    @3
    cG
    cbs
    cfv
    #
    @5
    @0
    cG
    cgrp
    wcel
    @3
    @7
    wcel
    cG
    tgpgrp
    @7
    cG
    @3
    @7
    eqid
    #
    @3
    eqid
    #
    grpidcl
    syl
    @0
    cJ
    @7
    ctopon
    cfv
    wcel
    @7
    @5
    wceq
    cG
    cJ
    @7
    tgpt1.j
    @8
    tgptopon
    @7
    cJ
    toponuni
    syl
    eleqtrd
    @2
    @6
    @4
    @3
    cJ
    @5
    @5
    eqid
    t1sncld
    expcom
    syl
    cG
    cJ
    @3
    @9
    tgpt1.j
    tgphaus
    sylibrd
    impbid2
end
