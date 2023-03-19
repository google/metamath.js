include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "eqid.mm"
include "simp3.mm"
include "wceq.mm"
include "cmgp.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "3ad2ant2.mm"
include "eleqtrd.mm"
include "cv.mm"
include "co.mm"
include "simp2.mm"
include "eqsstr3d.mm"
include "sselda.mm"
include "wa.mm"
include "cmulr.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "syl.mm"
include "adantr.mm"
include "oveqd.mm"
include "ringlidm.mm"
include "3ad2antl1.mm"
include "eqtr3d.mm"
include "syldan.mm"
include "ringridm.mm"
include "ismgmid2.mm"

theorem ringidss
  let cA: class A
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cM: class M
  let vy: setvar y
  assume ringidss.g: |- M = ( ( mulGrp ` R ) |`s A )
  assume ringidss.b: |- B = ( Base ` R )
  assume ringidss.u: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ A C_ B /\ .1. e. A ) -> .1. = ( 0g ` M ) )

  proof
    cR
    crg
    wcel
    #
    cA
    cB
    wss
    #
    c.1
    cA
    wcel
    #
    w3a
    #
    vy
    cM
    cbs
    cfv
    #
    cM
    cplusg
    cfv
    #
    c.1
    cM
    cM
    c0g
    cfv
    #
    @4
    eqid
    @6
    eqid
    @5
    eqid
    @3
    c.1
    cA
    @4
    @0
    @1
    @2
    simp3
    @1
    @0
    cA
    @4
    wceq
    @2
    cA
    cB
    cM
    cR
    cmgp
    cfv
    #
    ringidss.g
    cB
    cR
    @7
    @7
    eqid
    #
    ringidss.b
    mgpbas
    ressbas2
    3ad2ant2
    #
    eleqtrd
    @3
    vy
    cv
    #
    @4
    wcel
    #
    @10
    cB
    wcel
    #
    c.1
    @10
    @5
    co
    #
    @10
    wceq
    @3
    @4
    cB
    @10
    @3
    @4
    cA
    cB
    @9
    @0
    @1
    @2
    simp2
    eqsstr3d
    sselda
    #
    @3
    @12
    wa
    #
    c.1
    @10
    cR
    cmulr
    cfv
    #
    co
    #
    @13
    @10
    @15
    @16
    @5
    c.1
    @10
    @3
    @16
    @5
    wceq
    #
    @12
    @3
    cA
    cvv
    wcel
    @18
    @3
    cA
    @4
    cvv
    @9
    cM
    cbs
    fvex
    syl6eqel
    cA
    @16
    @7
    cM
    cvv
    ringidss.g
    cR
    @16
    @7
    @8
    @16
    eqid
    #
    mgpplusg
    ressplusg
    syl
    adantr
    #
    oveqd
    @0
    @1
    @12
    @17
    @10
    wceq
    @2
    cB
    cR
    @16
    c.1
    @10
    ringidss.b
    @19
    ringidss.u
    ringlidm
    3ad2antl1
    eqtr3d
    syldan
    @3
    @11
    @12
    @10
    c.1
    @5
    co
    #
    @10
    wceq
    @14
    @15
    @10
    c.1
    @16
    co
    #
    @21
    @10
    @15
    @16
    @5
    @10
    c.1
    @20
    oveqd
    @0
    @1
    @12
    @22
    @10
    wceq
    @2
    cB
    cR
    @16
    c.1
    @10
    ringidss.b
    @19
    ringidss.u
    ringridm
    3ad2antl1
    eqtr3d
    syldan
    ismgmid2
end
