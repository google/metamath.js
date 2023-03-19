include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cmnd.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "w3a.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmulr.mm"
include "wsbc.mm"
include "cplusg.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simpllr.mm"
include "simpr.mm"
include "eqidd.mm"
include "simplr.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "df-ring.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isring
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cG: class G
  let vb: setvar b
  let vp: setvar p
  let vr: setvar r
  let vt: setvar t
  assume isring.b: |- B = ( Base ` R )
  assume isring.g: |- G = ( mulGrp ` R )
  assume isring.p: |- .+ = ( +g ` R )
  assume isring.t: |- .x. = ( .r ` R )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint b p
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint p r
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint .+ b
  disjoint .+ p
  disjoint .+ r
  disjoint .+ t
  disjoint R b
  disjoint R p
  disjoint R r
  disjoint R t
  disjoint G r
  disjoint .x. b
  disjoint .x. p
  disjoint .x. r
  disjoint .x. t
  assert |- ( R e. Ring <-> ( R e. Grp /\ G e. Mnd /\ A. x e. B A. y e. B A. z e. B ( ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) ) /\ ( ( x .+ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) ) ) )

  proof
    cR
    crg
    wcel
    cR
    cgrp
    wcel
    #
    cG
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @2
    @3
    c.x
    co
    #
    @2
    @4
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @2
    @3
    c.pl
    co
    #
    @4
    c.x
    co
    #
    @8
    @3
    @4
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    wa
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    wa
    @0
    @1
    @19
    w3a
    vr
    cv
    #
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @2
    @3
    @4
    vp
    cv
    #
    co
    #
    vt
    cv
    #
    co
    #
    @2
    @3
    @26
    co
    #
    @2
    @4
    @26
    co
    #
    @24
    co
    #
    wceq
    #
    @2
    @3
    @24
    co
    #
    @4
    @26
    co
    #
    @29
    @3
    @4
    @26
    co
    #
    @24
    co
    #
    wceq
    #
    wa
    #
    vz
    vb
    cv
    #
    wral
    #
    vy
    @38
    wral
    #
    vx
    @38
    wral
    #
    vt
    @21
    cmulr
    cfv
    #
    wsbc
    #
    vp
    @21
    cplusg
    cfv
    #
    wsbc
    #
    vb
    @21
    cbs
    cfv
    #
    wsbc
    #
    wa
    @20
    vr
    cR
    cgrp
    crg
    @21
    cR
    wceq
    #
    @23
    @1
    @47
    @19
    @48
    @22
    cG
    cmnd
    @48
    @22
    cR
    cmgp
    cfv
    cG
    @21
    cR
    cmgp
    fveq2
    isring.g
    syl6eqr
    eleq1d
    @48
    @45
    @19
    vb
    @46
    cB
    cvv
    @48
    @21
    cbs
    fvexd
    @48
    @46
    cR
    cbs
    cfv
    cB
    @21
    cR
    cbs
    fveq2
    isring.b
    syl6eqr
    @48
    @38
    cB
    wceq
    #
    wa
    #
    @43
    @19
    vp
    @44
    c.pl
    cvv
    @50
    @21
    cplusg
    fvexd
    @50
    @44
    cR
    cplusg
    cfv
    c.pl
    @50
    @21
    cR
    cplusg
    @48
    @49
    simpl
    fveq2d
    isring.p
    syl6eqr
    @50
    @24
    c.pl
    wceq
    #
    wa
    #
    @41
    @19
    vt
    @42
    c.x
    cvv
    @52
    @21
    cmulr
    fvexd
    @52
    @42
    cR
    cmulr
    cfv
    c.x
    @52
    @21
    cR
    cmulr
    @48
    @49
    @51
    simpll
    fveq2d
    isring.t
    syl6eqr
    @52
    @26
    c.x
    wceq
    #
    wa
    #
    @40
    @18
    vx
    @38
    cB
    @48
    @49
    @51
    @53
    simpllr
    #
    @54
    @39
    @17
    vy
    @38
    cB
    @55
    @54
    @37
    @16
    vz
    @38
    cB
    @55
    @54
    @31
    @10
    @36
    @15
    @54
    @27
    @6
    @30
    @9
    @54
    @2
    @2
    @25
    @5
    @26
    c.x
    @52
    @53
    simpr
    #
    @54
    @2
    eqidd
    @54
    @24
    c.pl
    @3
    @4
    @50
    @51
    @53
    simplr
    #
    oveqd
    oveq123d
    @54
    @28
    @7
    @29
    @8
    @24
    c.pl
    @57
    @54
    @26
    c.x
    @2
    @3
    @56
    oveqd
    @54
    @26
    c.x
    @2
    @4
    @56
    oveqd
    #
    oveq123d
    eqeq12d
    @54
    @33
    @12
    @35
    @14
    @54
    @32
    @11
    @4
    @4
    @26
    c.x
    @56
    @54
    @24
    c.pl
    @2
    @3
    @57
    oveqd
    @54
    @4
    eqidd
    oveq123d
    @54
    @29
    @8
    @34
    @13
    @24
    c.pl
    @57
    @58
    @54
    @26
    c.x
    @3
    @4
    @56
    oveqd
    oveq123d
    eqeq12d
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    sbcied2
    sbcied2
    sbcied2
    anbi12d
    vx
    vy
    vz
    vt
    vr
    vb
    vp
    df-ring
    elrab2
    @0
    @1
    @19
    3anass
    bitr4i
end
