include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "simpr.mm"
include "oveq1d.mm"
include "simpl1.mm"
include "simpl2.mm"
include "eqid.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "eqtr4d.mm"
include "ringlidm.mm"
include "3eqtr3d.mm"
include "ex.mm"

theorem ring1eq0
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume ring1eq0.b: |- B = ( Base ` R )
  assume ring1eq0.u: |- .1. = ( 1r ` R )
  assume ring1eq0.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ X e. B /\ Y e. B ) -> ( .1. = .0. -> X = Y ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    c.1
    c.0
    wceq
    #
    cX
    cY
    wceq
    @3
    @4
    wa
    #
    c.1
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    cY
    @6
    co
    #
    cX
    cY
    @5
    @7
    c.0
    cX
    @6
    co
    #
    @8
    @5
    c.1
    c.0
    cX
    @6
    @3
    @4
    simpr
    #
    oveq1d
    @5
    @8
    c.0
    cY
    @6
    co
    #
    @9
    @5
    c.1
    c.0
    cY
    @6
    @10
    oveq1d
    @5
    @9
    c.0
    @11
    @5
    @0
    @1
    @9
    c.0
    wceq
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    cB
    cR
    @6
    cX
    c.0
    ring1eq0.b
    @6
    eqid
    #
    ring1eq0.z
    ringlz
    syl2anc
    @5
    @0
    @2
    @11
    c.0
    wceq
    @12
    @0
    @1
    @2
    @4
    simpl3
    #
    cB
    cR
    @6
    cY
    c.0
    ring1eq0.b
    @14
    ring1eq0.z
    ringlz
    syl2anc
    eqtr4d
    eqtr4d
    eqtr4d
    @5
    @0
    @1
    @7
    cX
    wceq
    @12
    @13
    cB
    cR
    @6
    c.1
    cX
    ring1eq0.b
    @14
    ring1eq0.u
    ringlidm
    syl2anc
    @5
    @0
    @2
    @8
    cY
    wceq
    @12
    @15
    cB
    cR
    @6
    c.1
    cY
    ring1eq0.b
    @14
    ring1eq0.u
    ringlidm
    syl2anc
    3eqtr3d
    ex
end
