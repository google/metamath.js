include "cphl.mm"
include "wcel.mm"
include "clvec.mm"
include "csr.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmhm.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "c0g.mm"
include "cstv.mm"
include "csca.mm"
include "wsbc.mm"
include "cip.mm"
include "cbs.mm"
include "cvv.mm"
include "fvexd.mm"
include "id.mm"
include "simpll.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "eleq1d.mm"
include "simpllr.mm"
include "simplll.mm"
include "eqtrd.mm"
include "simplr.mm"
include "oveqd.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "eqeq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "fveq12d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "df-phl.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isphl
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let c.xi: class .,
  let c.as: class .*
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  assume isphl.v: |- V = ( Base ` W )
  assume isphl.f: |- F = ( Scalar ` W )
  assume isphl.h: |- ., = ( .i ` W )
  assume isphl.o: |- .0. = ( 0g ` W )
  assume isphl.i: |- .* = ( *r ` F )
  assume isphl.z: |- Z = ( 0g ` F )

  disjoint x y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint f g
  disjoint f h
  disjoint f v
  disjoint F f
  disjoint g h
  disjoint g v
  disjoint F g
  disjoint h v
  disjoint F h
  disjoint F v
  disjoint ., f
  disjoint ., g
  disjoint ., h
  disjoint ., v
  disjoint f x
  disjoint f y
  disjoint V f
  disjoint g x
  disjoint g y
  disjoint V g
  disjoint h x
  disjoint h y
  disjoint V h
  disjoint v x
  disjoint v y
  disjoint V v
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint W v
  disjoint .* f
  disjoint .* g
  disjoint .* h
  disjoint .* v
  disjoint .0. f
  disjoint .0. g
  disjoint .0. h
  disjoint .0. v
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z v
  assert |- ( W e. PreHil <-> ( W e. LVec /\ F e. *Ring /\ A. x e. V ( ( y e. V |-> ( y ., x ) ) e. ( W LMHom ( ringLMod ` F ) ) /\ ( ( x ., x ) = Z -> x = .0. ) /\ A. y e. V ( .* ` ( x ., y ) ) = ( y ., x ) ) ) )

  proof
    cW
    cphl
    wcel
    cW
    clvec
    wcel
    #
    cF
    csr
    wcel
    #
    vy
    cV
    vy
    cv
    #
    vx
    cv
    #
    c.xi
    co
    #
    cmpt
    #
    cW
    cF
    crglmod
    cfv
    #
    clmhm
    co
    #
    wcel
    #
    @3
    @3
    c.xi
    co
    #
    cZ
    wceq
    #
    @3
    c.0
    wceq
    #
    wi
    #
    @3
    @2
    c.xi
    co
    #
    c.as
    cfv
    #
    @4
    wceq
    #
    vy
    cV
    wral
    #
    w3a
    #
    vx
    cV
    wral
    #
    wa
    #
    wa
    @0
    @1
    @18
    w3a
    vf
    cv
    #
    csr
    wcel
    #
    vy
    vv
    cv
    #
    @2
    @3
    vh
    cv
    #
    co
    #
    cmpt
    #
    vg
    cv
    #
    @20
    crglmod
    cfv
    #
    clmhm
    co
    #
    wcel
    #
    @3
    @3
    @23
    co
    #
    @20
    c0g
    cfv
    #
    wceq
    #
    @3
    @26
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    @3
    @2
    @23
    co
    #
    @20
    cstv
    cfv
    #
    cfv
    #
    @24
    wceq
    #
    vy
    @22
    wral
    #
    w3a
    #
    vx
    @22
    wral
    #
    wa
    #
    vf
    @26
    csca
    cfv
    #
    wsbc
    #
    vh
    @26
    cip
    cfv
    #
    wsbc
    #
    vv
    @26
    cbs
    cfv
    #
    wsbc
    @19
    vg
    cW
    clvec
    cphl
    @26
    cW
    wceq
    #
    @47
    @19
    vv
    @48
    cvv
    @49
    @26
    cbs
    fvexd
    @49
    @22
    @48
    wceq
    #
    wa
    #
    @45
    @19
    vh
    @46
    cvv
    @51
    @26
    cip
    fvexd
    @51
    @23
    @46
    wceq
    #
    wa
    #
    @43
    @19
    vf
    @44
    cvv
    @53
    @26
    csca
    fvexd
    @53
    @20
    @44
    wceq
    #
    wa
    #
    @21
    @1
    @42
    @18
    @55
    @20
    cF
    csr
    @54
    @53
    @20
    @44
    cF
    @54
    id
    @53
    @44
    cW
    csca
    cfv
    cF
    @53
    @26
    cW
    csca
    @49
    @50
    @52
    simpll
    fveq2d
    isphl.f
    syl6eqr
    sylan9eqr
    #
    eleq1d
    @55
    @41
    @17
    vx
    @22
    cV
    @55
    @22
    @48
    cV
    @49
    @50
    @52
    @54
    simpllr
    @55
    @48
    cW
    cbs
    cfv
    cV
    @55
    @26
    cW
    cbs
    @49
    @50
    @52
    @54
    simplll
    #
    fveq2d
    isphl.v
    syl6eqr
    eqtrd
    #
    @55
    @29
    @8
    @35
    @12
    @40
    @16
    @55
    @25
    @5
    @28
    @7
    @55
    vy
    @22
    @24
    cV
    @4
    @58
    @55
    @23
    c.xi
    @2
    @3
    @55
    @23
    @46
    c.xi
    @51
    @52
    @54
    simplr
    @55
    @46
    cW
    cip
    cfv
    c.xi
    @55
    @26
    cW
    cip
    @57
    fveq2d
    isphl.h
    syl6eqr
    eqtrd
    #
    oveqd
    #
    mpteq12dv
    @55
    @26
    cW
    @27
    @6
    clmhm
    @57
    @55
    @20
    cF
    crglmod
    @56
    fveq2d
    oveq12d
    eleq12d
    @55
    @32
    @10
    @34
    @11
    @55
    @30
    @9
    @31
    cZ
    @55
    @23
    c.xi
    @3
    @3
    @59
    oveqd
    @55
    @31
    cF
    c0g
    cfv
    cZ
    @55
    @20
    cF
    c0g
    @56
    fveq2d
    isphl.z
    syl6eqr
    eqeq12d
    @55
    @33
    c.0
    @3
    @55
    @33
    cW
    c0g
    cfv
    c.0
    @55
    @26
    cW
    c0g
    @57
    fveq2d
    isphl.o
    syl6eqr
    eqeq2d
    imbi12d
    @55
    @39
    @15
    vy
    @22
    cV
    @58
    @55
    @38
    @14
    @24
    @4
    @55
    @36
    @13
    @37
    c.as
    @55
    @37
    cF
    cstv
    cfv
    c.as
    @55
    @20
    cF
    cstv
    @56
    fveq2d
    isphl.i
    syl6eqr
    @55
    @23
    c.xi
    @3
    @2
    @59
    oveqd
    fveq12d
    @60
    eqeq12d
    raleqbidv
    3anbi123d
    raleqbidv
    anbi12d
    sbcied
    sbcied
    sbcied
    vx
    vy
    vv
    vf
    vg
    vh
    df-phl
    elrab2
    @0
    @1
    @18
    3anass
    bitr4i
end
