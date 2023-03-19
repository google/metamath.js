include "wcel.mm"
include "cvv.mm"
include "chg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "clcd.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "chdma.mm"
include "wsbc.mm"
include "csca.mm"
include "cdvh.mm"
include "cab.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "eleq2d.mm"
include "sbceqbid.mm"
include "sbcbidv.mm"
include "abbidv.mm"
include "mpteq12dv.mm"
include "df-hgmap.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem hgmapffval
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vm: setvar m
  let cH: class H
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume hgmapval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint a b
  disjoint a m
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint K a
  disjoint b m
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint K b
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
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint k w
  disjoint H k
  disjoint a k
  disjoint b k
  disjoint k m
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint K k
  assert |- ( K e. X -> ( HGMap ` K ) = ( w e. H |-> { a | [. ( ( DVecH ` K ) ` w ) / u ]. [. ( Base ` ( Scalar ` u ) ) / b ]. [. ( ( HDMap ` K ) ` w ) / m ]. a e. ( x e. b |-> ( iota_ y e. b A. v e. ( Base ` u ) ( m ` ( x ( .s ` u ) v ) ) = ( y ( .s ` ( ( LCDual ` K ) ` w ) ) ( m ` v ) ) ) ) } ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    chg
    cfv
    vw
    cH
    va
    cv
    #
    vx
    vb
    cv
    #
    vx
    cv
    vv
    cv
    #
    vu
    cv
    #
    cvsca
    cfv
    co
    vm
    cv
    #
    cfv
    #
    vy
    cv
    #
    @2
    @4
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
    @3
    cbs
    cfv
    #
    wral
    #
    vy
    @1
    crio
    #
    cmpt
    #
    wcel
    #
    vm
    @8
    cK
    chdma
    cfv
    #
    cfv
    #
    wsbc
    #
    vb
    @3
    csca
    cfv
    cbs
    cfv
    #
    wsbc
    #
    vu
    @8
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
    wceq
    cK
    cX
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    @0
    vx
    @1
    @5
    @6
    @7
    @8
    @29
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
    @14
    wral
    #
    vy
    @1
    crio
    #
    cmpt
    #
    wcel
    #
    vm
    @8
    @29
    chdma
    cfv
    #
    cfv
    #
    wsbc
    #
    vb
    @22
    wsbc
    #
    vu
    @8
    @29
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
    @28
    cvv
    chg
    @29
    cK
    wceq
    #
    vw
    @30
    @47
    cH
    @27
    @48
    @30
    cK
    clh
    cfv
    #
    cH
    @29
    cK
    clh
    fveq2
    hgmapval.h
    syl6eqr
    @48
    @46
    @26
    va
    @48
    @43
    @23
    vu
    @45
    @25
    @48
    @8
    @44
    @24
    @29
    cK
    cdvh
    fveq2
    fveq1d
    @48
    @42
    @21
    vb
    @22
    @48
    @39
    @18
    vm
    @41
    @20
    @48
    @8
    @40
    @19
    @29
    cK
    chdma
    fveq2
    fveq1d
    @48
    @38
    @17
    @0
    @48
    vx
    @1
    @37
    @16
    @48
    @36
    @15
    vy
    @1
    @48
    @35
    @13
    vv
    @14
    @48
    @34
    @12
    @5
    @48
    @33
    @11
    @6
    @7
    @48
    @32
    @10
    cvsca
    @48
    @8
    @31
    @9
    @29
    cK
    clcd
    fveq2
    fveq1d
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
    abbidv
    mpteq12dv
    vx
    vy
    vw
    vv
    vu
    vk
    vm
    va
    vb
    df-hgmap
    vw
    cH
    @27
    cH
    @49
    cvv
    hgmapval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
