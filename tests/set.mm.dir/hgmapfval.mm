include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "cvsca.mm"
include "clcd.mm"
include "cbs.mm"
include "chdma.mm"
include "wsbc.mm"
include "csca.mm"
include "cdvh.mm"
include "cab.mm"
include "chg.mm"
include "hgmapffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "eleq2d.mm"
include "sbceqbid.mm"
include "sbcbidv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wb.mm"
include "w3a.mm"
include "simp2.mm"
include "simp1.mm"
include "eqtrd.mm"
include "simp3.mm"
include "fveq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "syld3an2.mm"
include "sbc3ie.mm"
include "syl6bb.mm"
include "abbi1dv.mm"
include "eqid.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syl.mm"

theorem hgmapfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cM: class M
  let cV: class V
  let cW: class W
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vu: setvar u
  assume hgmapval.h: |- H = ( LHyp ` K )
  assume hgmapfval.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapfval.v: |- V = ( Base ` U )
  assume hgmapfval.t: |- .x. = ( .s ` U )
  assume hgmapfval.r: |- R = ( Scalar ` U )
  assume hgmapfval.b: |- B = ( Base ` R )
  assume hgmapfval.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmapfval.s: |- .xb = ( .s ` C )
  assume hgmapfval.m: |- M = ( ( HDMap ` K ) ` W )
  assume hgmapfval.i: |- I = ( ( HGMap ` K ) ` W )
  assume hgmapfval.k: |- ( ph -> ( K e. Y /\ W e. H ) )

  disjoint v x
  disjoint v y
  disjoint K v
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint V v
  disjoint W v
  disjoint W x
  disjoint W y
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint a b
  disjoint a k
  disjoint a m
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint K a
  disjoint b k
  disjoint b m
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint K b
  disjoint k m
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint K m
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B u
  disjoint B w
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M u
  disjoint M w
  disjoint .xb a
  disjoint .xb b
  disjoint .xb m
  disjoint .xb u
  disjoint .xb w
  disjoint .x. a
  disjoint .x. b
  disjoint .x. m
  disjoint .x. u
  disjoint .x. w
  disjoint U b
  disjoint U m
  disjoint U u
  disjoint V a
  disjoint V b
  disjoint V m
  disjoint V u
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W m
  disjoint W u
  disjoint W w
  assert |- ( ph -> I = ( x e. B |-> ( iota_ y e. B A. v e. V ( M ` ( x .x. v ) ) = ( y .xb ( M ` v ) ) ) ) )

  proof
    wph
    cK
    cY
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cI
    vx
    cB
    vx
    cv
    #
    vv
    cv
    #
    c.x
    co
    #
    cM
    cfv
    #
    vy
    cv
    #
    @3
    cM
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vv
    cV
    wral
    #
    vy
    cB
    crio
    #
    cmpt
    #
    wceq
    hgmapfval.k
    @0
    @1
    cI
    cW
    vw
    cH
    va
    cv
    #
    vx
    vb
    cv
    #
    @2
    @3
    vu
    cv
    #
    cvsca
    cfv
    #
    co
    #
    vm
    cv
    #
    cfv
    #
    @6
    @3
    @18
    cfv
    #
    vw
    cv
    #
    cK
    clcd
    cfv
    #
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vv
    @15
    cbs
    cfv
    #
    wral
    #
    vy
    @14
    crio
    #
    cmpt
    #
    wcel
    #
    vm
    @21
    cK
    chdma
    cfv
    #
    cfv
    #
    wsbc
    #
    vb
    @15
    csca
    cfv
    #
    cbs
    cfv
    #
    wsbc
    #
    vu
    @21
    cK
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    #
    cfv
    #
    @12
    @0
    cI
    cW
    cK
    chg
    cfv
    #
    cfv
    @43
    hgmapfval.i
    @0
    cW
    @44
    @42
    vx
    vy
    vw
    vv
    vu
    vm
    cH
    cK
    cY
    va
    vb
    hgmapval.h
    hgmapffval
    fveq1d
    syl5eq
    vw
    cW
    @41
    @12
    cH
    @42
    @21
    cW
    wceq
    #
    @40
    va
    @12
    @45
    @40
    @13
    vx
    @14
    @19
    @6
    @20
    cW
    @22
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vv
    @27
    wral
    #
    vy
    @14
    crio
    #
    cmpt
    #
    wcel
    #
    vm
    cM
    wsbc
    #
    vb
    @36
    wsbc
    #
    vu
    cU
    wsbc
    @13
    @12
    wcel
    #
    @45
    @37
    @55
    vu
    @39
    cU
    @45
    @39
    cW
    @38
    cfv
    #
    cU
    @21
    cW
    @38
    fveq2
    hgmapfval.u
    syl6eqr
    @45
    @34
    @54
    vb
    @36
    @45
    @31
    @53
    vm
    @33
    cM
    @45
    @33
    cW
    @32
    cfv
    #
    cM
    @21
    cW
    @32
    fveq2
    hgmapfval.m
    syl6eqr
    @45
    @30
    @52
    @13
    @45
    vx
    @14
    @29
    @51
    @45
    @28
    @50
    vy
    @14
    @45
    @26
    @49
    vv
    @27
    @45
    @25
    @48
    @19
    @45
    @24
    @47
    @6
    @20
    @45
    @23
    @46
    cvsca
    @21
    cW
    @22
    fveq2
    fveq2d
    oveqd
    eqeq2d
    ralbidv
    riotabidv
    mpteq2dv
    eleq2d
    sbceqbid
    sbcbidv
    sbceqbid
    @53
    @56
    vu
    vb
    vm
    cU
    @36
    cM
    cU
    @57
    cvv
    hgmapfval.u
    cW
    @38
    fvex
    eqeltri
    @35
    cbs
    fvex
    cM
    @58
    cvv
    hgmapfval.m
    cW
    @32
    fvex
    eqeltri
    @15
    cU
    wceq
    #
    @14
    cB
    wceq
    #
    @14
    @36
    wceq
    #
    @18
    cM
    wceq
    #
    @53
    @56
    wb
    @59
    @61
    @62
    w3a
    #
    @14
    cR
    cbs
    cfv
    #
    cB
    @63
    @14
    @36
    @64
    @59
    @61
    @62
    simp2
    @63
    @35
    cR
    cbs
    @63
    @35
    cU
    csca
    cfv
    cR
    @63
    @15
    cU
    csca
    @59
    @61
    @62
    simp1
    fveq2d
    hgmapfval.r
    syl6eqr
    fveq2d
    eqtrd
    hgmapfval.b
    syl6eqr
    @59
    @60
    @62
    w3a
    #
    @52
    @12
    @13
    @65
    vx
    @14
    @51
    cB
    @11
    @59
    @60
    @62
    simp2
    #
    @65
    @50
    @10
    vy
    @14
    cB
    @66
    @65
    @49
    @9
    vv
    @27
    cV
    @65
    @27
    cU
    cbs
    cfv
    cV
    @65
    @15
    cU
    cbs
    @59
    @60
    @62
    simp1
    #
    fveq2d
    hgmapfval.v
    syl6eqr
    @65
    @19
    @5
    @48
    @8
    @65
    @17
    @4
    @18
    cM
    @59
    @60
    @62
    simp3
    #
    @65
    @16
    c.x
    @2
    @3
    @65
    @16
    cU
    cvsca
    cfv
    c.x
    @65
    @15
    cU
    cvsca
    @67
    fveq2d
    hgmapfval.t
    syl6eqr
    oveqd
    fveq12d
    @65
    @6
    @6
    @20
    @7
    @47
    c.xb
    @65
    @47
    cC
    cvsca
    cfv
    c.xb
    @65
    @46
    cC
    cvsca
    @65
    @46
    @46
    cC
    @65
    @46
    eqidd
    hgmapfval.c
    syl6eqr
    fveq2d
    hgmapfval.s
    syl6eqr
    @65
    @6
    eqidd
    @65
    @3
    @18
    cM
    @68
    fveq1d
    oveq123d
    eqeq12d
    raleqbidv
    riotaeqbidv
    mpteq12dv
    eleq2d
    syld3an2
    sbc3ie
    syl6bb
    abbi1dv
    @42
    eqid
    vx
    cB
    @11
    cB
    @64
    cvv
    hgmapfval.b
    cR
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    sylan9eq
    syl
end
