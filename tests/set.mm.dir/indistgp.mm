include "cgrp.mm"
include "wcel.mm"
include "c0.mm"
include "cpr.mm"
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
include "indistopon.mm"
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
include "oveq2d.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "cnindis.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "istgp2.mm"
include "syl3anbrc.mm"

theorem indistgp
  let cB: class B
  let cG: class G
  let cJ: class J
  assume distgp.1: |- B = ( Base ` G )
  assume distgp.2: |- J = ( TopOpen ` G )


  assert |- ( ( G e. Grp /\ J = { (/) , B } ) -> G e. TopGrp )

  proof
    cG
    cgrp
    wcel
    #
    cJ
    c0
    cB
    cpr
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
    indistopon
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
    elmap
    sylibr
    @3
    @7
    @6
    @1
    ccn
    co
    #
    @15
    @3
    cJ
    @1
    @6
    ccn
    @10
    oveq2d
    @3
    @6
    @14
    ctopon
    cfv
    wcel
    #
    @11
    @18
    @15
    wceq
    @3
    @9
    @9
    @19
    @13
    @13
    cJ
    cJ
    cB
    cB
    txtopon
    syl2anc
    @12
    cB
    @6
    cvv
    @14
    cnindis
    sylancl
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
