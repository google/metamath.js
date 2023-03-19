include "cfrgr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "c2.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "wf1o.mm"
include "wa.mm"
include "cfv.mm"
include "wi.mm"
include "eleq1w.mm"
include "fveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "numclwlk2lem2fv.mm"
include "chvarv.mm"
include "3adant1.mm"
include "imp.mm"
include "numclwlk2lem2f.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "cs1.mm"
include "cconcat.mm"
include "numclwwlk2lem1.mm"
include "cwwlksn.mm"
include "clsw.mm"
include "wne.mm"
include "crab.mm"
include "wb.mm"
include "numclwwlkovq.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "chash.mm"
include "cword.mm"
include "cvtx.mm"
include "cn0.mm"
include "wwlknbp1.mm"
include "3simpc.mm"
include "syl.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "anbi1i.mm"
include "sylibr.mm"
include "simpll.mm"
include "cclwwlkn.mm"
include "cmin.mm"
include "id.mm"
include "2nn.mm"
include "a1i.mm"
include "nnaddcld.mm"
include "numclwwlkovh.mm"
include "sylan2.mm"
include "neeq12d.mm"
include "adantl.mm"
include "clwwlknbp.mm"
include "lencl.mm"
include "simprr.mm"
include "df-2.mm"
include "oveq2d.mm"
include "nncn.mm"
include "1cnd.mm"
include "addassd.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "biimpcd.mm"
include "adantr.mm"
include "impcom.mm"
include "ad3antlr.mm"
include "jca.mm"
include "exp31.mm"
include "sylan.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "ancoms.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ex.mm"
include "nfcv.mm"
include "cmpt2.mm"
include "nfmpt21.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "reuccats1.mm"
include "simp3d.mm"
include "eqcomd.mm"
include "ad4antr.mm"
include "opeq2d.mm"
include "reubidva.mm"
include "mpbird.mm"
include "mpd.mm"
include "f1ompt.mm"
include "sylanbrc.mm"

theorem numclwlk2lem2f1o
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W
  let vy: setvar y
  let vu: setvar u
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )
  assume numclwwlk.h: |- H = ( v e. V , n e. NN |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) =/= ( w ` 0 ) ) } )
  assume numclwwlk.r: |- R = ( x e. ( X H ( N + 2 ) ) |-> ( x substr <. 0 , ( N + 1 ) >. ) )

  disjoint G w
  disjoint G x
  disjoint w x
  disjoint H x
  disjoint N x
  disjoint Q x
  disjoint V x
  disjoint X x
  disjoint G v
  disjoint v w
  disjoint v x
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint V w
  disjoint W x
  disjoint G y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint H y
  disjoint N y
  disjoint R y
  disjoint V y
  disjoint X y
  disjoint G u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint H u
  disjoint N u
  disjoint Q u
  disjoint R u
  disjoint V u
  disjoint X u
  disjoint G f
  disjoint f w
  disjoint K w
  disjoint N f
  disjoint V f
  disjoint X f
  disjoint G i
  disjoint N i
  disjoint W i
  disjoint W v
  disjoint W w
  assert |- ( ( G e. FriendGraph /\ X e. V /\ N e. NN ) -> R : ( X H ( N + 2 ) ) -1-1-onto-> ( X Q N ) )

  proof
    cG
    cfrgr
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cc0
    cN
    c1
    caddc
    co
    #
    cop
    #
    csubstr
    co
    #
    cX
    cN
    cQ
    co
    #
    wcel
    #
    vx
    cX
    cN
    c2
    caddc
    co
    #
    cH
    co
    #
    wral
    vu
    cv
    #
    @7
    wceq
    #
    vx
    @11
    wreu
    #
    vu
    @8
    wral
    @11
    @8
    cR
    wf1o
    @3
    @9
    vx
    @11
    @3
    @4
    @11
    wcel
    #
    wa
    @4
    cR
    cfv
    #
    @7
    @8
    @3
    @15
    @16
    @7
    wceq
    #
    @1
    @2
    @15
    @17
    wi
    #
    @0
    @1
    @2
    wa
    #
    vy
    cv
    #
    @11
    wcel
    #
    @20
    cR
    cfv
    #
    @20
    @6
    csubstr
    co
    #
    wceq
    #
    wi
    #
    wi
    @19
    @18
    wi
    vy
    vx
    @20
    @4
    wceq
    #
    @25
    @18
    @19
    @26
    @21
    @15
    @24
    @17
    vy
    vx
    @11
    eleq1w
    @26
    @22
    @16
    @23
    @7
    @20
    @4
    cR
    fveq2
    @20
    @4
    @6
    csubstr
    oveq1
    eqeq12d
    imbi12d
    imbi2d
    vx
    vw
    vv
    cQ
    cR
    vn
    cG
    cH
    cN
    cV
    @20
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlk.r
    numclwlk2lem2fv
    chvarv
    3adant1
    imp
    @3
    @11
    @8
    @4
    cR
    vx
    vw
    vv
    cQ
    cR
    vn
    cG
    cH
    cN
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlk.r
    numclwlk2lem2f
    ffvelrnda
    eqeltrrd
    ralrimiva
    @3
    @14
    vu
    @8
    @3
    @12
    @8
    wcel
    #
    wa
    @12
    vv
    cv
    #
    cs1
    cconcat
    co
    @11
    wcel
    vv
    cV
    wreu
    #
    @14
    @3
    @27
    @29
    vw
    vv
    cQ
    vn
    cG
    cH
    cN
    cV
    @12
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlk2lem1
    imp
    @3
    @27
    @29
    @14
    wi
    #
    @3
    @27
    @12
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @12
    cfv
    #
    cX
    wceq
    #
    @12
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    wa
    #
    @30
    @3
    @27
    @12
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    @39
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    vw
    @31
    crab
    #
    wcel
    #
    @38
    @1
    @2
    @27
    @46
    wb
    @0
    @19
    @8
    @45
    @12
    vw
    vv
    cQ
    vn
    cG
    cN
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlkovq
    eleq2d
    3adant1
    @44
    @37
    vw
    @12
    @31
    @39
    @12
    wceq
    #
    @41
    @34
    @43
    @36
    @47
    @40
    @33
    cX
    cc0
    @39
    @12
    fveq1
    eqeq1d
    @47
    @42
    @35
    cX
    @39
    @12
    clsw
    fveq2
    neeq1d
    anbi12d
    elrab
    syl6bb
    @38
    @3
    @30
    @38
    @3
    @29
    @14
    @38
    @3
    wa
    #
    @29
    wa
    #
    @14
    @12
    @4
    cc0
    @12
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    wceq
    #
    vx
    @11
    wreu
    #
    @48
    @29
    @54
    @48
    @12
    cV
    cword
    #
    wcel
    #
    @4
    @55
    wcel
    #
    @4
    chash
    cfv
    #
    @50
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    vx
    @11
    wral
    #
    wa
    #
    @29
    @54
    wi
    @38
    @3
    @63
    @32
    @3
    @63
    wi
    #
    @37
    @32
    @56
    @50
    @5
    wceq
    #
    wa
    #
    @64
    @32
    @12
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @65
    wa
    #
    @66
    @32
    cN
    cn0
    wcel
    #
    @69
    @65
    w3a
    @70
    cG
    cN
    @12
    wwlknbp1
    #
    @71
    @69
    @65
    3simpc
    syl
    @56
    @69
    @65
    @55
    @68
    @12
    cV
    @67
    numclwwlk.v
    wrdeqi
    eleq2i
    anbi1i
    sylibr
    @66
    @3
    @63
    @66
    @3
    wa
    #
    @56
    @62
    @56
    @65
    @3
    simpll
    @73
    @61
    vx
    @11
    @73
    @15
    @4
    @10
    cG
    cclwwlkn
    co
    #
    wcel
    #
    cc0
    @4
    cfv
    #
    cX
    wceq
    #
    @10
    c2
    cmin
    co
    #
    @4
    cfv
    #
    @76
    wne
    #
    wa
    #
    wa
    #
    @61
    @3
    @15
    @82
    wb
    #
    @66
    @1
    @2
    @83
    @0
    @19
    @15
    @4
    @41
    @78
    @39
    cfv
    #
    @40
    wne
    #
    wa
    #
    vw
    @74
    crab
    #
    wcel
    @82
    @19
    @11
    @87
    @4
    @2
    @1
    @10
    cn
    wcel
    @11
    @87
    wceq
    @2
    cN
    c2
    @2
    id
    c2
    cn
    wcel
    @2
    2nn
    a1i
    nnaddcld
    vw
    vv
    cQ
    vn
    cG
    cH
    @10
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlkovh
    sylan2
    eleq2d
    @86
    @81
    vw
    @4
    @74
    @39
    @4
    wceq
    #
    @41
    @77
    @85
    @80
    @88
    @40
    @76
    cX
    cc0
    @39
    @4
    fveq1
    #
    eqeq1d
    @88
    @84
    @79
    @40
    @76
    @78
    @39
    @4
    fveq1
    @89
    neeq12d
    anbi12d
    elrab
    syl6bb
    3adant1
    adantl
    @82
    @73
    @61
    @75
    @73
    @61
    wi
    #
    @81
    @75
    @57
    @58
    @10
    wceq
    #
    wa
    @90
    cG
    @10
    cV
    @4
    numclwwlk.v
    clwwlknbp
    @91
    @57
    @90
    @73
    @91
    @57
    wa
    #
    @61
    @3
    @66
    @92
    @61
    wi
    #
    @2
    @0
    @66
    @93
    wi
    @1
    @66
    @2
    @93
    @56
    @50
    cn0
    wcel
    #
    @65
    @2
    @93
    wi
    cV
    @12
    lencl
    @94
    @65
    wa
    #
    @2
    @92
    @61
    @95
    @2
    wa
    #
    @92
    wa
    #
    @57
    @60
    @96
    @91
    @57
    simprr
    @97
    @58
    @5
    c1
    caddc
    co
    #
    @59
    @92
    @96
    @58
    @98
    wceq
    #
    @91
    @96
    @99
    wi
    @57
    @96
    @91
    @99
    @96
    @10
    @98
    @58
    @2
    @10
    @98
    wceq
    @95
    @2
    @10
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @98
    @2
    c2
    @100
    cN
    caddc
    c2
    @100
    wceq
    @2
    df-2
    a1i
    oveq2d
    @2
    cN
    c1
    c1
    cN
    nncn
    @2
    1cnd
    #
    @101
    addassd
    eqtr4d
    adantl
    eqeq2d
    biimpcd
    adantr
    impcom
    @65
    @59
    @98
    wceq
    @94
    @2
    @92
    @50
    @5
    c1
    caddc
    oveq1
    ad3antlr
    eqtr4d
    jca
    exp31
    sylan
    com12
    3ad2ant3
    impcom
    com12
    ancoms
    syl
    adantr
    com12
    sylbid
    ralrimiv
    jca
    ex
    syl
    adantr
    imp
    vx
    vv
    cV
    @12
    @11
    vv
    cX
    @10
    cH
    vv
    cX
    nfcv
    vv
    cH
    vv
    vn
    cV
    cn
    @40
    @28
    wceq
    vn
    cv
    #
    c2
    cmin
    co
    @39
    cfv
    @40
    wne
    wa
    vw
    @102
    cG
    cclwwlkn
    co
    crab
    #
    cmpt2
    numclwwlk.h
    vv
    vn
    cV
    cn
    @103
    nfmpt21
    nfcxfr
    vv
    @10
    nfcv
    nfov
    reuccats1
    syl
    imp
    @49
    @13
    @53
    vx
    @11
    @49
    @15
    wa
    #
    @7
    @52
    @12
    @104
    @6
    @51
    @4
    csubstr
    @104
    @5
    @50
    cc0
    @32
    @5
    @50
    wceq
    @37
    @3
    @29
    @15
    @32
    @50
    @5
    @32
    @71
    @69
    @65
    @72
    simp3d
    eqcomd
    ad4antr
    opeq2d
    oveq2d
    eqeq2d
    reubidva
    mpbird
    exp31
    com12
    sylbid
    imp
    mpd
    ralrimiva
    vx
    vu
    @11
    @8
    @7
    cR
    numclwwlk.r
    f1ompt
    sylanbrc
end
