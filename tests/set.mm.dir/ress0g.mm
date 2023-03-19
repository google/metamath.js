include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cplusg.mm"
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
include "ressplusg.mm"
include "syl.mm"
include "simp2.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "simpl1.mm"
include "sselda.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "mndrid.mm"
include "grpidd.mm"

theorem ress0g
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.0: class .0.
  let vx: setvar x
  assume ress0g.s: |- S = ( R |`s A )
  assume ress0g.b: |- B = ( Base ` R )
  assume ress0g.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Mnd /\ .0. e. A /\ A C_ B ) -> .0. = ( 0g ` S ) )

  proof
    cR
    cmnd
    wcel
    #
    c.0
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
    cR
    cplusg
    cfv
    #
    cS
    c.0
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
    ress0g.s
    ress0g.b
    ressbas2
    3ad2ant3
    @3
    cA
    cvv
    wcel
    #
    @4
    cS
    cplusg
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
    ress0g.b
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
    @4
    cR
    cS
    cvv
    ress0g.s
    @4
    eqid
    #
    ressplusg
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
    c.0
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
    @4
    cR
    @8
    c.0
    ress0g.b
    @7
    ress0g.0
    mndlid
    syl2anc
    @10
    @0
    @11
    @8
    c.0
    @4
    co
    @8
    wceq
    @12
    @13
    cB
    @4
    cR
    @8
    c.0
    ress0g.b
    @7
    ress0g.0
    mndrid
    syl2anc
    grpidd
end
