include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "cun.mm"
include "wi.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "elfzonn0.mm"
include "adantl.mm"
include "lencl.mm"
include "cn.mm"
include "elfzo0.mm"
include "cr.mm"
include "nn0re.mm"
include "adantr.mm"
include "peano2rem.mm"
include "syl.mm"
include "3jca.mm"
include "ltm1d.mm"
include "lttr.mm"
include "expcomd.mm"
include "sylc.mm"
include "impancom.mm"
include "3adant2.mm"
include "sylbi.mm"
include "syl5com.mm"
include "imp.mm"
include "simplr.mm"
include "ccat2s1fvw.mm"
include "syl31anc.mm"
include "eqcomd.mm"
include "simpl.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "1red.mm"
include "ltaddsubd.mm"
include "biimprd.mm"
include "mpan9.mm"
include "adantlr.mm"
include "syl2anc.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "3adant3.mm"
include "com12.mm"
include "a1dd.mm"
include "imp31.mm"
include "ax-1.mm"
include "oveq1.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "2p1e3.mm"
include "a1i.mm"
include "oveq2d.mm"
include "uznn0sub.mm"
include "eqeltrd.mm"
include "ancoms.mm"
include "ex.mm"
include "simpl2.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eqid.mm"
include "2a1i.mm"
include "imdistani.mm"
include "simp2l.mm"
include "simp2r.mm"
include "ccatw2s1p1.mm"
include "syl12anc.mm"
include "eqtrd.mm"
include "lsw.mm"
include "expcom.mm"
include "com23.mm"
include "exp520.mm"
include "com14.mm"
include "3ad2ant3.mm"
include "syld.mm"
include "com25.mm"
include "3imp.mm"
include "impcom.mm"
include "mpanl2.mm"
include "ccatw2s1p2.mm"
include "com13.mm"
include "simpr.mm"
include "ovex.mm"
include "fvex.mm"
include "fveq2.mm"
include "ralpr.mm"
include "sylanbrc.mm"
include "ralunb.mm"

theorem clwwlknonex2lem2
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume clwwlknonex2.v: |- V = ( Vtx ` G )
  assume clwwlknonex2.e: |- E = ( Edg ` G )

  disjoint E i
  disjoint V i
  disjoint W i
  disjoint X i
  disjoint Y i
  assert |- ( ( ( ( X e. V /\ Y e. V /\ N e. ( ZZ>= ` 3 ) ) /\ ( ( W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) /\ ( # ` W ) = ( N - 2 ) /\ ( W ` 0 ) = X ) ) /\ { X , Y } e. E ) -> A. i e. ( ( 0 ..^ ( ( # ` W ) - 1 ) ) u. { ( ( # ` W ) - 1 ) , ( # ` W ) } ) { ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` i ) , ( ( ( W ++ <" X "> ) ++ <" Y "> ) ` ( i + 1 ) ) } e. E )

  proof
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cW
    cV
    cword
    #
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    #
    @6
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cW
    clsw
    cfv
    #
    cc0
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @12
    cN
    c2
    cmin
    co
    #
    wceq
    #
    @17
    cX
    wceq
    #
    w3a
    #
    wa
    #
    cX
    cY
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @6
    cW
    cX
    cs1
    cconcat
    co
    cY
    cs1
    cconcat
    co
    #
    cfv
    #
    @8
    @29
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    @14
    wral
    #
    @33
    vi
    @13
    @12
    cpr
    #
    wral
    #
    @33
    vi
    @14
    @35
    cun
    wral
    @3
    @24
    @27
    @34
    @0
    @1
    @24
    @27
    @34
    wi
    wi
    @2
    @0
    @1
    wa
    #
    @24
    @34
    @27
    @24
    @37
    @34
    @20
    @22
    @37
    @34
    wi
    #
    @23
    @5
    @15
    @38
    @19
    @5
    @37
    @15
    @34
    @5
    @37
    wa
    #
    @15
    @34
    @39
    @11
    @33
    vi
    @14
    @39
    @6
    @14
    wcel
    #
    wa
    #
    @10
    @32
    cE
    @41
    @7
    @30
    @9
    @31
    @41
    @30
    @7
    @41
    @5
    @6
    cn0
    wcel
    #
    @6
    @12
    clt
    wbr
    #
    @37
    @30
    @7
    wceq
    @5
    @37
    @40
    simpll
    @40
    @42
    @39
    @6
    @13
    elfzonn0
    adantl
    @39
    @40
    @43
    @5
    @40
    @43
    wi
    @37
    @5
    @12
    cn0
    wcel
    #
    @40
    @43
    cV
    cW
    lencl
    #
    @40
    @42
    @13
    cn
    wcel
    #
    @6
    @13
    clt
    wbr
    #
    w3a
    #
    @44
    @43
    wi
    #
    @6
    @13
    elfzo0
    #
    @42
    @47
    @49
    @46
    @42
    @44
    @47
    @43
    @42
    @44
    wa
    #
    @6
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    w3a
    #
    @13
    @12
    clt
    wbr
    #
    @47
    @43
    wi
    @51
    @52
    @53
    @54
    @42
    @52
    @44
    @6
    nn0re
    adantr
    #
    @44
    @53
    @42
    @44
    @54
    @53
    @12
    nn0re
    #
    @12
    peano2rem
    syl
    adantl
    @44
    @54
    @42
    @58
    adantl
    #
    3jca
    @44
    @56
    @42
    @44
    @12
    @58
    ltm1d
    adantl
    @55
    @47
    @56
    @43
    @6
    @13
    @12
    lttr
    expcomd
    sylc
    impancom
    3adant2
    sylbi
    syl5com
    adantr
    imp
    @5
    @37
    @40
    simplr
    #
    @6
    cV
    cW
    cX
    cY
    ccat2s1fvw
    syl31anc
    eqcomd
    @41
    @31
    @9
    @41
    @5
    @8
    cn0
    wcel
    #
    @8
    @12
    clt
    wbr
    #
    w3a
    #
    @37
    @31
    @9
    wceq
    @5
    @40
    @63
    @37
    @5
    @40
    wa
    @5
    @61
    @62
    @5
    @40
    simpl
    @40
    @61
    @5
    @40
    @48
    @61
    @50
    @42
    @46
    @61
    @47
    @6
    peano2nn0
    3ad2ant1
    sylbi
    adantl
    @5
    @44
    @40
    @62
    @45
    @40
    @48
    @44
    @62
    wi
    #
    @50
    @42
    @47
    @64
    @46
    @42
    @44
    @47
    @62
    @51
    @62
    @47
    @51
    @6
    c1
    @12
    @57
    @51
    1red
    @59
    ltaddsubd
    biimprd
    impancom
    3adant2
    sylbi
    mpan9
    3jca
    adantlr
    @60
    @8
    cV
    cW
    cX
    cY
    ccat2s1fvw
    syl2anc
    eqcomd
    preq12d
    eleq1d
    ralbidva
    biimpd
    impancom
    3adant3
    3ad2ant1
    com12
    a1dd
    3adant3
    imp31
    @28
    @13
    @29
    cfv
    #
    @13
    c1
    caddc
    co
    #
    @29
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @12
    @29
    cfv
    #
    @12
    c1
    caddc
    co
    #
    @29
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @36
    @25
    @27
    @69
    @24
    @3
    @27
    @69
    wi
    #
    @20
    @22
    @23
    @3
    @75
    wi
    #
    @5
    @19
    @22
    @23
    @76
    wi
    wi
    @15
    @3
    @22
    @23
    @5
    @19
    wa
    #
    @75
    @3
    @27
    @23
    @77
    @22
    @69
    @3
    @27
    @37
    @23
    @77
    @22
    @69
    wi
    #
    wi
    wi
    #
    @0
    @1
    @27
    @37
    wi
    @2
    @37
    @27
    ax-1
    3adant3
    @2
    @0
    @37
    @79
    wi
    @1
    @77
    @37
    @23
    @2
    @78
    @77
    @37
    @23
    @2
    @22
    @69
    @77
    @37
    @23
    w3a
    #
    @2
    @22
    wa
    #
    wa
    #
    @68
    @13
    cW
    cfv
    #
    cX
    cpr
    #
    cE
    @82
    @65
    @83
    @67
    cX
    @82
    @5
    @13
    cn0
    wcel
    #
    @56
    w3a
    #
    @37
    @65
    @83
    wceq
    @80
    @81
    @86
    @77
    @37
    @81
    @86
    wi
    #
    @23
    @5
    @87
    @19
    @5
    @81
    @86
    @5
    @81
    wa
    #
    @5
    @85
    @56
    @5
    @81
    simpl
    @81
    @85
    @5
    @22
    @2
    @85
    @22
    @2
    wa
    @13
    @21
    c1
    cmin
    co
    #
    cn0
    @22
    @13
    @89
    wceq
    @2
    @12
    @21
    c1
    cmin
    oveq1
    adantr
    @2
    @89
    cn0
    wcel
    @22
    @2
    @89
    cN
    c2
    c1
    caddc
    co
    #
    cmin
    co
    #
    cn0
    @2
    cN
    c2
    c1
    c3
    cN
    eluzelcn
    @2
    2cnd
    @2
    1cnd
    subsub4d
    @2
    @91
    cN
    c3
    cmin
    co
    cn0
    @2
    @90
    c3
    cN
    cmin
    @90
    c3
    wceq
    @2
    2p1e3
    a1i
    oveq2d
    c3
    cN
    uznn0sub
    eqeltrd
    eqeltrd
    adantl
    eqeltrd
    ancoms
    adantl
    @88
    @12
    @5
    @54
    @81
    @5
    @44
    @54
    @45
    @58
    syl
    adantr
    ltm1d
    3jca
    ex
    adantr
    3ad2ant1
    imp
    @77
    @37
    @23
    @81
    simpl2
    @13
    cV
    cW
    cX
    cY
    ccat2s1fvw
    syl2anc
    @80
    @67
    cX
    wceq
    @81
    @80
    @67
    @70
    cX
    @80
    @66
    @12
    @29
    @77
    @37
    @66
    @12
    wceq
    #
    @23
    @5
    @92
    @19
    @5
    @44
    @92
    @45
    @44
    @12
    cc
    wcel
    c1
    cc
    wcel
    @92
    @12
    nn0cn
    ax-1cn
    @12
    c1
    npcan
    sylancl
    syl
    adantr
    3ad2ant1
    fveq2d
    @80
    @5
    @12
    @12
    wceq
    #
    wa
    #
    @0
    @1
    @70
    cX
    wceq
    #
    @77
    @37
    @94
    @23
    @5
    @19
    @93
    @93
    @5
    @19
    @12
    eqid
    #
    2a1i
    imdistani
    3ad2ant1
    @77
    @0
    @1
    @23
    simp2l
    @77
    @0
    @1
    @23
    simp2r
    @12
    cV
    cW
    cX
    cY
    ccatw2s1p1
    #
    syl12anc
    eqtrd
    adantr
    preq12d
    @80
    @84
    cE
    wcel
    #
    @81
    @77
    @23
    @98
    @37
    @5
    @19
    @23
    @98
    @5
    @23
    @19
    @98
    @23
    @5
    @19
    @98
    wi
    @23
    @5
    wa
    #
    @19
    @98
    @99
    @18
    @84
    cE
    @99
    @16
    @83
    @17
    cX
    @5
    @16
    @83
    wceq
    @23
    cW
    @4
    lsw
    adantl
    @23
    @5
    simpl
    preq12d
    eleq1d
    biimpd
    expcom
    com23
    imp31
    3adant2
    adantr
    eqeltrd
    exp520
    com14
    3ad2ant3
    syld
    com25
    com14
    3adant2
    3imp
    impcom
    imp
    @28
    @73
    @26
    cE
    @3
    @24
    @27
    @73
    @26
    wceq
    #
    @0
    @1
    @24
    @27
    @100
    wi
    #
    wi
    @2
    @24
    @37
    @101
    @20
    @22
    @37
    @101
    wi
    #
    @23
    @5
    @15
    @102
    @19
    @27
    @37
    @5
    @100
    @37
    @5
    @100
    wi
    wi
    @27
    @5
    @37
    @100
    @39
    @70
    cX
    @72
    cY
    @5
    @93
    @37
    @95
    @96
    @97
    mpanl2
    @5
    @93
    @37
    @72
    cY
    wceq
    @96
    @12
    cV
    cW
    cX
    cY
    ccatw2s1p2
    mpanl2
    preq12d
    expcom
    a1i
    com13
    3ad2ant1
    3ad2ant1
    com12
    3adant3
    imp31
    @25
    @27
    simpr
    eqeltrd
    @33
    @69
    @74
    vi
    @13
    @12
    @12
    c1
    cmin
    ovex
    cW
    chash
    fvex
    @6
    @13
    wceq
    #
    @32
    @68
    cE
    @103
    @30
    @65
    @31
    @67
    @6
    @13
    @29
    fveq2
    @103
    @8
    @66
    @29
    @6
    @13
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    @6
    @12
    wceq
    #
    @32
    @73
    cE
    @104
    @30
    @70
    @31
    @72
    @6
    @12
    @29
    fveq2
    @104
    @8
    @71
    @29
    @6
    @12
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralpr
    sylanbrc
    @33
    vi
    @14
    @35
    ralunb
    sylanbrc
end
