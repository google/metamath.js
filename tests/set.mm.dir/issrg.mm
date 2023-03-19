include "ccmn.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wsbc.mm"
include "csrg.mm"
include "w3a.mm"
include "eleq1i.mm"
include "bicomi.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cplusg.mm"
include "cmulr.mm"
include "a1i.mm"
include "c0g.mm"
include "simplll.mm"
include "simplr.mm"
include "eqidd.mm"
include "simpllr.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "simpr.mm"
include "sbcied.mm"
include "sbc2ie.mm"
include "anbi12i.mm"
include "anbi2i.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl6eqr.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "df-srg.mm"
include "elrab2.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem issrg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cG: class G
  let c.0: class .0.
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vt: setvar t
  assume issrg.b: |- B = ( Base ` R )
  assume issrg.g: |- G = ( mulGrp ` R )
  assume issrg.p: |- .+ = ( +g ` R )
  assume issrg.t: |- .x. = ( .r ` R )
  assume issrg.0: |- .0. = ( 0g ` R )

  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint b n
  disjoint b p
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .+ b
  disjoint n p
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint .+ n
  disjoint p r
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint .+ p
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint .+ r
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .+ t
  disjoint .0. b
  disjoint .0. n
  disjoint .0. p
  disjoint .0. r
  disjoint .0. t
  disjoint G r
  disjoint .x. b
  disjoint .x. n
  disjoint .x. p
  disjoint .x. r
  disjoint .x. t
  disjoint B b
  disjoint B n
  disjoint B p
  disjoint B r
  disjoint B t
  disjoint R b
  disjoint R n
  disjoint R p
  disjoint R r
  disjoint R t
  assert |- ( R e. SRing <-> ( R e. CMnd /\ G e. Mnd /\ A. x e. B ( A. y e. B A. z e. B ( ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) ) /\ ( ( x .+ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) ) /\ ( ( .0. .x. x ) = .0. /\ ( x .x. .0. ) = .0. ) ) ) )

  proof
    cR
    ccmn
    wcel
    #
    cR
    cmgp
    cfv
    #
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
    @3
    @4
    @8
    co
    #
    @3
    @5
    @8
    co
    #
    @6
    co
    #
    wceq
    #
    @3
    @4
    @6
    co
    #
    @5
    @8
    co
    #
    @11
    @4
    @5
    @8
    co
    #
    @6
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
    @20
    wral
    #
    vn
    cv
    #
    @3
    @8
    co
    #
    @23
    wceq
    #
    @3
    @23
    @8
    co
    #
    @23
    wceq
    #
    wa
    #
    wa
    #
    vx
    @20
    wral
    #
    vn
    c.0
    wsbc
    #
    vt
    c.x
    wsbc
    #
    vp
    c.pl
    wsbc
    #
    vb
    cB
    wsbc
    #
    wa
    #
    wa
    @0
    cG
    cmnd
    wcel
    #
    @3
    @4
    @5
    c.pl
    co
    #
    c.x
    co
    #
    @3
    @4
    c.x
    co
    #
    @3
    @5
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @3
    @4
    c.pl
    co
    #
    @5
    c.x
    co
    #
    @40
    @4
    @5
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
    c.0
    @3
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    wa
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    #
    wa
    cR
    csrg
    wcel
    @0
    @36
    @57
    w3a
    @35
    @58
    @0
    @2
    @36
    @34
    @57
    @36
    @2
    cG
    @1
    cmnd
    issrg.g
    eleq1i
    bicomi
    @32
    @57
    vb
    vp
    cB
    c.pl
    cB
    cR
    cbs
    cfv
    #
    cvv
    issrg.b
    cR
    cbs
    fvex
    eqeltri
    c.pl
    cR
    cplusg
    cfv
    #
    cvv
    issrg.p
    cR
    cplusg
    fvex
    eqeltri
    @20
    cB
    wceq
    #
    @6
    c.pl
    wceq
    #
    wa
    #
    @31
    @57
    vt
    c.x
    cvv
    c.x
    cvv
    wcel
    @63
    c.x
    cR
    cmulr
    cfv
    #
    cvv
    issrg.t
    cR
    cmulr
    fvex
    eqeltri
    a1i
    @63
    @8
    c.x
    wceq
    #
    wa
    #
    @30
    @57
    vn
    c.0
    cvv
    c.0
    cvv
    wcel
    @66
    c.0
    cR
    c0g
    cfv
    #
    cvv
    issrg.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    @66
    @23
    c.0
    wceq
    #
    wa
    #
    @29
    @56
    vx
    @20
    cB
    @61
    @62
    @65
    @68
    simplll
    #
    @69
    @22
    @50
    @28
    @55
    @69
    @21
    @49
    vy
    @20
    cB
    @70
    @69
    @19
    @48
    vz
    @20
    cB
    @70
    @69
    @13
    @42
    @18
    @47
    @69
    @9
    @38
    @12
    @41
    @69
    @3
    @3
    @7
    @37
    @8
    c.x
    @63
    @65
    @68
    simplr
    #
    @69
    @3
    eqidd
    #
    @69
    @6
    c.pl
    @4
    @5
    @61
    @62
    @65
    @68
    simpllr
    #
    oveqd
    oveq123d
    @69
    @10
    @39
    @11
    @40
    @6
    c.pl
    @73
    @69
    @8
    c.x
    @3
    @4
    @71
    oveqd
    @69
    @8
    c.x
    @3
    @5
    @71
    oveqd
    #
    oveq123d
    eqeq12d
    @69
    @15
    @44
    @17
    @46
    @69
    @14
    @43
    @5
    @5
    @8
    c.x
    @71
    @69
    @6
    c.pl
    @3
    @4
    @73
    oveqd
    @69
    @5
    eqidd
    oveq123d
    @69
    @11
    @40
    @16
    @45
    @6
    c.pl
    @73
    @74
    @69
    @8
    c.x
    @4
    @5
    @71
    oveqd
    oveq123d
    eqeq12d
    anbi12d
    raleqbidv
    raleqbidv
    @69
    @25
    @52
    @27
    @54
    @69
    @24
    @51
    @23
    c.0
    @69
    @23
    c.0
    @3
    @3
    @8
    c.x
    @71
    @66
    @68
    simpr
    #
    @72
    oveq123d
    @75
    eqeq12d
    @69
    @26
    @53
    @23
    c.0
    @69
    @3
    @3
    @23
    c.0
    @8
    c.x
    @71
    @72
    @75
    oveq123d
    @75
    eqeq12d
    anbi12d
    anbi12d
    raleqbidv
    sbcied
    sbcied
    sbc2ie
    anbi12i
    anbi2i
    vr
    cv
    #
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @30
    vn
    @76
    c0g
    cfv
    #
    wsbc
    #
    vt
    @76
    cmulr
    cfv
    #
    wsbc
    #
    vp
    @76
    cplusg
    cfv
    #
    wsbc
    #
    vb
    @76
    cbs
    cfv
    #
    wsbc
    #
    wa
    @35
    vr
    cR
    ccmn
    csrg
    @76
    cR
    wceq
    #
    @78
    @2
    @86
    @34
    @87
    @77
    @1
    cmnd
    @76
    cR
    cmgp
    fveq2
    eleq1d
    @87
    @84
    @33
    vb
    @85
    cB
    @87
    @85
    @59
    cB
    @76
    cR
    cbs
    fveq2
    issrg.b
    syl6eqr
    @87
    @82
    @32
    vp
    @83
    c.pl
    @87
    @83
    @60
    c.pl
    @76
    cR
    cplusg
    fveq2
    issrg.p
    syl6eqr
    @87
    @80
    @31
    vt
    @81
    c.x
    @87
    @81
    @64
    c.x
    @76
    cR
    cmulr
    fveq2
    issrg.t
    syl6eqr
    @87
    @30
    vn
    @79
    c.0
    @87
    @79
    @67
    c.0
    @76
    cR
    c0g
    fveq2
    issrg.0
    syl6eqr
    sbceq1d
    sbceqbid
    sbceqbid
    sbceqbid
    anbi12d
    vx
    vy
    vz
    vt
    vr
    vn
    vb
    vp
    df-srg
    elrab2
    @0
    @36
    @57
    3anass
    3bitr4i
end
