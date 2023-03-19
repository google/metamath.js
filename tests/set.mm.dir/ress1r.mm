include "crg.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "ressbas2.mm"
include "3ad2ant3.mm"
include "cvv.mm"
include "simp3.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssexg.mm"
include "sylancl.mm"
include "eqid.mm"
include "ressmulr.mm"
include "syl.mm"
include "simp2.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "simpl1.mm"
include "sselda.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "ringridm.mm"
include "rngurd.mm"

theorem ress1r
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let vx: setvar x
  assume ress1r.s: |- S = ( R |`s A )
  assume ress1r.b: |- B = ( Base ` R )
  assume ress1r.1: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ .1. e. A /\ A C_ B ) -> .1. = ( 1r ` S ) )

  proof
    cR
    crg
    wcel
    #
    c.1
    cA
    wcel
    #
    cA
    cB
    wss
    #
    w3a
    #
    vx
    cA
    cS
    cR
    cmulr
    cfv
    #
    c.1
    @2
    @0
    cA
    cS
    cbs
    cfv
    wceq
    @1
    cA
    cB
    cS
    cR
    ress1r.s
    ress1r.b
    ressbas2
    3ad2ant3
    @3
    cA
    cvv
    wcel
    #
    @4
    cS
    cmulr
    cfv
    wceq
    @3
    @2
    cB
    cvv
    wcel
    @5
    @0
    @1
    @2
    simp3
    #
    cB
    cR
    cbs
    cfv
    cvv
    ress1r.b
    cR
    cbs
    fvex
    eqeltri
    cA
    cB
    cvv
    ssexg
    sylancl
    cA
    cR
    cS
    @4
    cvv
    ress1r.s
    @4
    eqid
    #
    ressmulr
    syl
    @0
    @1
    @2
    simp2
    @3
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @0
    @8
    cB
    wcel
    #
    c.1
    @8
    @4
    co
    @8
    wceq
    @0
    @1
    @2
    @9
    simpl1
    #
    @3
    cA
    cB
    @8
    @6
    sselda
    #
    cB
    cR
    @4
    c.1
    @8
    ress1r.b
    @7
    ress1r.1
    ringlidm
    syl2anc
    @10
    @0
    @11
    @8
    c.1
    @4
    co
    @8
    wceq
    @12
    @13
    cB
    cR
    @4
    c.1
    @8
    ress1r.b
    @7
    ress1r.1
    ringridm
    syl2anc
    rngurd
end
