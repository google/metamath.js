include "cgrp.mm"
include "wcel.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "ctps.mm"
include "csg.mm"
include "cfv.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ctgp.mm"
include "simpl.mm"
include "ctopon.mm"
include "simpr.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "distopon.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "istps.mm"
include "sylibr.mm"
include "cxp.mm"
include "cmap.mm"
include "wf.mm"
include "eqid.mm"
include "grpsubf.mm"
include "adantr.mm"
include "xpex.mm"
include "elmap.mm"
include "oveq12d.mm"
include "txdis.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "cndis.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "istgp2.mm"
include "syl3anbrc.mm"

theorem distgp
  let cB: class B
  let cG: class G
  let cJ: class J
  assume distgp.1: |- B = ( Base ` G )
  assume distgp.2: |- J = ( TopOpen ` G )


  assert |- ( ( G e. Grp /\ J = ~P B ) -> G e. TopGrp )

  proof
    cG
    cgrp
    wcel
    #
    cJ
    cB
    cpw
    #
    wceq
    #
    wa
    #
    @0
    cG
    ctps
    wcel
    #
    cG
    csg
    cfv
    #
    cJ
    cJ
    ctx
    co
    #
    cJ
    ccn
    co
    #
    wcel
    cG
    ctgp
    wcel
    @0
    @2
    simpl
    @3
    cJ
    cB
    ctopon
    cfv
    #
    wcel
    #
    @4
    @3
    cJ
    @1
    @8
    @0
    @2
    simpr
    #
    cB
    cvv
    wcel
    #
    @1
    @8
    wcel
    cB
    cG
    cbs
    cfv
    cvv
    distgp.1
    cG
    cbs
    fvex
    eqeltri
    #
    cB
    cvv
    distopon
    ax-mp
    syl6eqel
    #
    cB
    cJ
    cG
    distgp.1
    distgp.2
    istps
    sylibr
    @3
    @5
    cB
    cB
    cB
    cxp
    #
    cmap
    co
    #
    @7
    @3
    @14
    cB
    @5
    wf
    #
    @5
    @15
    wcel
    @0
    @16
    @2
    cB
    cG
    @5
    distgp.1
    @5
    eqid
    #
    grpsubf
    adantr
    cB
    @14
    @5
    @12
    cB
    cB
    @12
    @12
    xpex
    #
    elmap
    sylibr
    @3
    @7
    @14
    cpw
    #
    cJ
    ccn
    co
    #
    @15
    @3
    @6
    @19
    cJ
    ccn
    @3
    @6
    @1
    @1
    ctx
    co
    #
    @19
    @3
    cJ
    @1
    cJ
    @1
    ctx
    @10
    @10
    oveq12d
    @11
    @11
    @21
    @19
    wceq
    @12
    @12
    cB
    cB
    cvv
    cvv
    txdis
    mp2an
    syl6eq
    oveq1d
    @3
    @14
    cvv
    wcel
    @9
    @20
    @15
    wceq
    @18
    @13
    @14
    cJ
    cvv
    cB
    cndis
    sylancr
    eqtrd
    eleqtrrd
    cG
    cJ
    @5
    distgp.2
    @17
    istgp2
    syl3anbrc
end
