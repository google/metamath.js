include "crng.mm"
include "wcel.mm"
include "cabl.mm"
include "csgrp.mm"
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
include "adantr.mm"
include "simpllr.mm"
include "simpr.mm"
include "eqidd.mm"
include "oveq.mm"
include "ad2antlr.mm"
include "oveq123d.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "sbcied2.mm"
include "df-rng0.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isrng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cG: class G
  let vb: setvar b
  let vr: setvar r
  let vt: setvar t
  let vp: setvar p
  let vk: setvar k
  assume isrng.b: |- B = ( Base ` R )
  assume isrng.g: |- G = ( mulGrp ` R )
  assume isrng.p: |- .+ = ( +g ` R )
  assume isrng.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint B b
  disjoint B r
  disjoint B t
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B p
  disjoint G r
  disjoint R b
  disjoint R r
  disjoint R t
  disjoint R p
  disjoint .x. b
  disjoint .x. r
  disjoint .x. t
  disjoint .x. p
  disjoint .+ p
  disjoint .+ b
  disjoint .+ r
  disjoint .+ t
  disjoint b p
  disjoint p r
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint k x
  assert |- ( R e. Rng <-> ( R e. Abel /\ G e. SGrp /\ A. x e. B A. y e. B A. z e. B ( ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) ) /\ ( ( x .+ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) ) ) )

  proof
    cR
    crng
    wcel
    cR
    cabl
    wcel
    #
    cG
    csgrp
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
    csgrp
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
    cabl
    crng
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
    csgrp
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
    isrng.g
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
    isrng.b
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
    #
    c.pl
    @48
    @44
    @51
    wceq
    @49
    @21
    cR
    cplusg
    fveq2
    adantr
    isrng.p
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
    @53
    @21
    cmulr
    fvexd
    @53
    @42
    cR
    cmulr
    cfv
    #
    c.x
    @50
    @42
    @54
    wceq
    #
    @52
    @48
    @55
    @49
    @21
    cR
    cmulr
    fveq2
    adantr
    adantr
    isrng.t
    syl6eqr
    @53
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
    @52
    @56
    simpllr
    #
    @57
    @39
    @17
    vy
    @38
    cB
    @58
    @57
    @37
    @16
    vz
    @38
    cB
    @58
    @57
    @31
    @10
    @36
    @15
    @57
    @27
    @6
    @30
    @9
    @57
    @2
    @2
    @25
    @5
    @26
    c.x
    @53
    @56
    simpr
    #
    @57
    @2
    eqidd
    @52
    @25
    @5
    wceq
    @50
    @56
    @3
    @4
    @24
    c.pl
    oveq
    ad2antlr
    oveq123d
    @57
    @28
    @7
    @29
    @8
    @24
    c.pl
    @53
    @52
    @56
    @50
    @52
    simpr
    adantr
    #
    @56
    @28
    @7
    wceq
    @53
    @2
    @3
    @26
    c.x
    oveq
    adantl
    @56
    @29
    @8
    wceq
    @53
    @2
    @4
    @26
    c.x
    oveq
    adantl
    #
    oveq123d
    eqeq12d
    @57
    @33
    @12
    @35
    @14
    @57
    @32
    @11
    @4
    @4
    @26
    c.x
    @59
    @52
    @32
    @11
    wceq
    @50
    @56
    @2
    @3
    @24
    c.pl
    oveq
    ad2antlr
    @57
    @4
    eqidd
    oveq123d
    @57
    @29
    @8
    @34
    @13
    @24
    c.pl
    @60
    @61
    @56
    @34
    @13
    wceq
    @53
    @3
    @4
    @26
    c.x
    oveq
    adantl
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
    vp
    vb
    df-rng0
    elrab2
    @0
    @1
    @19
    3anass
    bitr4i
end
