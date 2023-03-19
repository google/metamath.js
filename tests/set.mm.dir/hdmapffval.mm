include "wcel.mm"
include "cvv.mm"
include "chdma.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cun.mm"
include "wn.mm"
include "chvm.mm"
include "cotp.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "clcd.mm"
include "cbs.mm"
include "crio.mm"
include "cmpt.mm"
include "chdma1.mm"
include "wsbc.mm"
include "cdvh.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "cab.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "fveq1d.mm"
include "opeq12d.mm"
include "fveq2d.mm"
include "oteq2d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotaeqbidv.mm"
include "mpteq2dv.mm"
include "eleq2d.mm"
include "sbceqbid.mm"
include "sbcbidv.mm"
include "abbidv.mm"
include "mpteq12dv.mm"
include "df-hdmap.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem hdmapffval
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let ve: setvar e
  let vi: setvar i
  let cH: class H
  let cK: class K
  let cX: class X
  let va: setvar a
  let vk: setvar k
  assume hdmapval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint a e
  disjoint a i
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint K a
  disjoint e i
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint e y
  disjoint e z
  disjoint K e
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint K i
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint K t
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint K u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint K v
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint k w
  disjoint H k
  disjoint a k
  disjoint e k
  disjoint i k
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint k z
  disjoint K k
  assert |- ( K e. X -> ( HDMap ` K ) = ( w e. H |-> { a | [. <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` w ) ) >. / e ]. [. ( ( DVecH ` K ) ` w ) / u ]. [. ( Base ` u ) / v ]. [. ( ( HDMap1 ` K ) ` w ) / i ]. a e. ( t e. v |-> ( iota_ y e. ( Base ` ( ( LCDual ` K ) ` w ) ) A. z e. v ( -. z e. ( ( ( LSpan ` u ) ` { e } ) u. ( ( LSpan ` u ) ` { t } ) ) -> y = ( i ` <. z , ( i ` <. e , ( ( ( HVMap ` K ) ` w ) ` e ) , z >. ) , t >. ) ) ) ) } ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    chdma
    cfv
    vw
    cH
    va
    cv
    #
    vt
    vv
    cv
    #
    vz
    cv
    #
    ve
    cv
    #
    csn
    vu
    cv
    #
    clspn
    cfv
    #
    cfv
    vt
    cv
    #
    csn
    @5
    cfv
    cun
    wcel
    wn
    #
    vy
    cv
    #
    @2
    @3
    @3
    vw
    cv
    #
    cK
    chvm
    cfv
    #
    cfv
    #
    cfv
    #
    @2
    cotp
    #
    vi
    cv
    #
    cfv
    #
    @6
    cotp
    #
    @14
    cfv
    #
    wceq
    #
    wi
    #
    vz
    @1
    wral
    #
    vy
    @9
    cK
    clcd
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    wcel
    #
    vi
    @9
    cK
    chdma1
    cfv
    #
    cfv
    #
    wsbc
    #
    vv
    @4
    cbs
    cfv
    #
    wsbc
    #
    vu
    @9
    cK
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    ve
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    cid
    @9
    cK
    cltrn
    cfv
    #
    cfv
    #
    cres
    #
    cop
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
    vt
    @1
    @7
    @8
    @2
    @3
    @3
    @9
    @44
    chvm
    cfv
    #
    cfv
    #
    cfv
    #
    @2
    cotp
    #
    @14
    cfv
    #
    @6
    cotp
    #
    @14
    cfv
    #
    wceq
    #
    wi
    #
    vz
    @1
    wral
    #
    vy
    @9
    @44
    clcd
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    wcel
    #
    vi
    @9
    @44
    chdma1
    cfv
    #
    cfv
    #
    wsbc
    #
    vv
    @30
    wsbc
    #
    vu
    @9
    @44
    cdvh
    cfv
    #
    cfv
    #
    wsbc
    #
    ve
    cid
    @44
    cbs
    cfv
    #
    cres
    #
    cid
    @9
    @44
    cltrn
    cfv
    #
    cfv
    #
    cres
    #
    cop
    #
    wsbc
    #
    va
    cab
    #
    cmpt
    @43
    cvv
    chdma
    @44
    cK
    wceq
    #
    vw
    @45
    @76
    cH
    @42
    @77
    @45
    cK
    clh
    cfv
    #
    cH
    @44
    cK
    clh
    fveq2
    hdmapval.h
    syl6eqr
    @77
    @75
    @41
    va
    @77
    @68
    @34
    ve
    @74
    @40
    @77
    @70
    @36
    @73
    @39
    @77
    @69
    @35
    cid
    @44
    cK
    cbs
    fveq2
    reseq2d
    @77
    @72
    @38
    cid
    @77
    @9
    @71
    @37
    @44
    cK
    cltrn
    fveq2
    fveq1d
    reseq2d
    opeq12d
    @77
    @65
    @31
    vu
    @67
    @33
    @77
    @9
    @66
    @32
    @44
    cK
    cdvh
    fveq2
    fveq1d
    @77
    @64
    @29
    vv
    @30
    @77
    @61
    @26
    vi
    @63
    @28
    @77
    @9
    @62
    @27
    @44
    cK
    chdma1
    fveq2
    fveq1d
    @77
    @60
    @25
    @0
    @77
    vt
    @1
    @59
    @24
    @77
    @55
    @20
    vy
    @58
    @23
    @77
    @57
    @22
    cbs
    @77
    @9
    @56
    @21
    @44
    cK
    clcd
    fveq2
    fveq1d
    fveq2d
    @77
    @54
    @19
    vz
    @1
    @77
    @53
    @18
    @7
    @77
    @52
    @17
    @8
    @77
    @51
    @16
    @14
    @77
    @50
    @15
    @2
    @6
    @77
    @49
    @13
    @14
    @77
    @48
    @12
    @3
    @2
    @77
    @3
    @47
    @11
    @77
    @9
    @46
    @10
    @44
    cK
    chvm
    fveq2
    fveq1d
    fveq1d
    oteq2d
    fveq2d
    oteq2d
    fveq2d
    eqeq2d
    imbi2d
    ralbidv
    riotaeqbidv
    mpteq2dv
    eleq2d
    sbceqbid
    sbcbidv
    sbceqbid
    sbceqbid
    abbidv
    mpteq12dv
    vy
    vz
    vw
    vv
    vu
    vt
    ve
    vi
    vk
    va
    df-hdmap
    vw
    cH
    @42
    cH
    @78
    cvv
    hdmapval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
