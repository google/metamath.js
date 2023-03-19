include "cfrgr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "wa.mm"
include "cwwlksn.mm"
include "cfv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "cclwwlkn.mm"
include "cmin.mm"
include "crab.mm"
include "wb.mm"
include "id.mm"
include "2nn.mm"
include "a1i.mm"
include "nnaddcld.mm"
include "anim2i.mm"
include "3adant1.mm"
include "numclwwlkovh.mm"
include "eleq2d.mm"
include "syl.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "neeq12d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cuz.mm"
include "peano2nn.mm"
include "cz.mm"
include "nnz.mm"
include "2z.mm"
include "zaddcld.mm"
include "uzid.mm"
include "nncn.mm"
include "1cnd.mm"
include "addassd.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "simprl.mm"
include "wwlksubclwwlk.mm"
include "sylc.mm"
include "cc.mm"
include "pncan1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpbird.mm"
include "wi.mm"
include "cword.mm"
include "chash.mm"
include "clwwlknbp.mm"
include "cfz.mm"
include "simprr.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "nnre.mm"
include "lep1d.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "2cnd.mm"
include "addsubass.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "syl3anc.mm"
include "elfzp1b.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "oveq2.mm"
include "ad2antrl.mm"
include "swrd0fv0.mm"
include "ex.mm"
include "adantl.mm"
include "impcom.mm"
include "simpl.mm"
include "swrd0fvlsw.mm"
include "pncand.mm"
include "eqtr4d.mm"
include "eqtr2d.mm"
include "neeq1d.mm"
include "biimpcd.mm"
include "neeq2.mm"
include "eqcoms.mm"
include "mpancom.mm"
include "exp31.mm"
include "com23.mm"
include "ancoms.mm"
include "imp.mm"
include "com12.mm"
include "sylbid.mm"
include "3simpc.mm"
include "numclwwlkovq.mm"
include "fveq2.mm"
include "fmptd.mm"

theorem numclwlk2lem2f
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
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  let cW: class W
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
  assert |- ( ( G e. FriendGraph /\ X e. V /\ N e. NN ) -> R : ( X H ( N + 2 ) ) --> ( X Q N ) )

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
    cX
    cN
    c2
    caddc
    co
    #
    cH
    co
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
    csubstr
    co
    #
    cX
    cN
    cQ
    co
    #
    cR
    @3
    @6
    @5
    wcel
    #
    wa
    #
    @8
    @9
    wcel
    #
    @8
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @8
    cfv
    #
    cX
    wceq
    #
    @8
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
    @3
    @10
    @20
    @3
    @10
    @6
    @4
    cG
    cclwwlkn
    co
    #
    wcel
    #
    cc0
    @6
    cfv
    #
    cX
    wceq
    #
    @4
    c2
    cmin
    co
    #
    @6
    cfv
    #
    @23
    wne
    #
    wa
    #
    wa
    #
    @20
    @3
    @10
    @6
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    @25
    @30
    cfv
    #
    @31
    wne
    #
    wa
    #
    vw
    @21
    crab
    #
    wcel
    #
    @29
    @3
    @1
    @4
    cn
    wcel
    #
    wa
    #
    @10
    @37
    wb
    @1
    @2
    @39
    @0
    @2
    @38
    @1
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
    anim2i
    3adant1
    @39
    @5
    @36
    @6
    vw
    vv
    cQ
    vn
    cG
    cH
    @4
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlkovh
    eleq2d
    syl
    @35
    @28
    vw
    @6
    @21
    @30
    @6
    wceq
    #
    @32
    @24
    @34
    @27
    @40
    @31
    @23
    cX
    cc0
    @30
    @6
    fveq1
    #
    eqeq1d
    @40
    @33
    @26
    @31
    @23
    @25
    @30
    @6
    fveq1
    @41
    neeq12d
    anbi12d
    elrab
    syl6bb
    @3
    @29
    @20
    @3
    @29
    wa
    #
    @14
    @19
    @42
    @14
    @8
    @7
    c1
    cmin
    co
    #
    cG
    cwwlksn
    co
    #
    wcel
    #
    @42
    @7
    cn
    wcel
    #
    @4
    @7
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    @22
    @45
    @3
    @50
    @29
    @2
    @0
    @50
    @1
    @2
    @46
    @49
    cN
    peano2nn
    @2
    @4
    @4
    cuz
    cfv
    #
    @48
    @2
    @4
    cz
    wcel
    #
    @4
    @51
    wcel
    @2
    cN
    c2
    cN
    nnz
    #
    c2
    cz
    wcel
    @2
    2z
    a1i
    zaddcld
    #
    @4
    uzid
    syl
    @2
    @47
    @4
    cuz
    @2
    @47
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @4
    @2
    cN
    c1
    c1
    cN
    nncn
    #
    @2
    1cnd
    #
    @57
    addassd
    @2
    @55
    c2
    cN
    caddc
    @55
    c2
    wceq
    @2
    1p1e2
    a1i
    oveq2d
    eqtrd
    fveq2d
    eleqtrrd
    jca
    3ad2ant3
    adantr
    @3
    @22
    @28
    simprl
    cG
    @7
    @4
    @6
    wwlksubclwwlk
    sylc
    @3
    @14
    @45
    wb
    #
    @29
    @2
    @0
    @58
    @1
    @2
    @13
    @44
    @8
    @2
    cN
    @43
    cG
    cwwlksn
    @2
    cN
    cc
    wcel
    #
    cN
    @43
    wceq
    @56
    @59
    @43
    cN
    cN
    pncan1
    #
    eqcomd
    syl
    oveq1d
    eleq2d
    3ad2ant3
    adantr
    mpbird
    @3
    @29
    @19
    @1
    @2
    @29
    @19
    wi
    @0
    @29
    @1
    @2
    wa
    #
    @19
    @22
    @28
    @61
    @19
    wi
    #
    @22
    @6
    cV
    cword
    wcel
    #
    @6
    chash
    cfv
    #
    @4
    wceq
    #
    wa
    @28
    @62
    wi
    #
    cG
    @4
    cV
    @6
    numclwwlk.v
    clwwlknbp
    @65
    @63
    @66
    @65
    @63
    wa
    #
    @61
    @28
    @19
    @67
    @61
    @28
    @19
    @24
    @67
    @61
    wa
    #
    @28
    wa
    #
    @19
    @68
    @24
    @27
    simprl
    @24
    @69
    wa
    #
    @16
    @18
    @70
    @15
    @23
    cX
    @68
    @15
    @23
    wceq
    #
    @24
    @28
    @61
    @67
    @71
    @2
    @67
    @71
    wi
    @1
    @2
    @67
    @71
    @2
    @67
    wa
    #
    @63
    @7
    c1
    @64
    cfz
    co
    #
    wcel
    #
    @71
    @2
    @65
    @63
    simprr
    #
    @72
    @74
    @7
    c1
    @4
    cfz
    co
    #
    wcel
    #
    @2
    @77
    @67
    @2
    cN
    cc0
    @4
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    @77
    @2
    cN
    cc0
    @7
    cfz
    co
    #
    @79
    @2
    cN
    cn0
    wcel
    #
    @7
    cn0
    wcel
    #
    cN
    @7
    cle
    wbr
    cN
    @81
    wcel
    cN
    nnnn0
    #
    @2
    @82
    @83
    @84
    cN
    peano2nn0
    syl
    @2
    cN
    cN
    nnre
    lep1d
    cN
    @7
    elfz2nn0
    syl3anbrc
    @2
    @78
    @7
    cc0
    cfz
    @2
    @59
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @78
    @7
    wceq
    @56
    @2
    2cnd
    #
    @57
    @59
    @85
    @86
    w3a
    @78
    cN
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @7
    cN
    c2
    c1
    addsubass
    @88
    c1
    cN
    caddc
    2m1e1
    oveq2i
    syl6eq
    syl3anc
    oveq2d
    eleqtrrd
    @2
    cN
    cz
    wcel
    @52
    @80
    @77
    wb
    @53
    @54
    cN
    @4
    elfzp1b
    syl2anc
    mpbid
    adantr
    @65
    @74
    @77
    wb
    @2
    @63
    @65
    @73
    @76
    @7
    @64
    @4
    c1
    cfz
    oveq2
    eleq2d
    ad2antrl
    mpbird
    #
    @7
    cV
    @6
    swrd0fv0
    syl2anc
    ex
    adantl
    impcom
    ad2antrl
    @24
    @69
    simpl
    eqtrd
    @70
    @18
    @17
    @23
    wne
    #
    @69
    @90
    @24
    @28
    @68
    @90
    @27
    @68
    @90
    wi
    @24
    @68
    @27
    @90
    @68
    @26
    @17
    @23
    @61
    @67
    @26
    @17
    wceq
    #
    @2
    @67
    @91
    wi
    @1
    @2
    @67
    @91
    @72
    @17
    @43
    @6
    cfv
    #
    @26
    @72
    @63
    @74
    @17
    @92
    wceq
    @75
    @89
    @7
    cV
    @6
    swrd0fvlsw
    syl2anc
    @2
    @92
    @26
    wceq
    @67
    @2
    @43
    @25
    @6
    @2
    @43
    cN
    @25
    @2
    @59
    @43
    cN
    wceq
    @56
    @60
    syl
    @2
    cN
    c2
    @56
    @87
    pncand
    eqtr4d
    fveq2d
    adantr
    eqtr2d
    ex
    adantl
    impcom
    neeq1d
    biimpcd
    adantl
    impcom
    adantl
    @24
    @18
    @90
    wb
    #
    @69
    @93
    cX
    @23
    cX
    @23
    @17
    neeq2
    eqcoms
    adantr
    mpbird
    jca
    mpancom
    exp31
    com23
    ancoms
    syl
    imp
    com12
    3adant1
    imp
    jca
    ex
    sylbid
    imp
    @11
    @12
    @8
    @32
    @30
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    vw
    @13
    crab
    #
    wcel
    @20
    @11
    @9
    @97
    @8
    @11
    @61
    @9
    @97
    wceq
    @3
    @61
    @10
    @0
    @1
    @2
    3simpc
    adantr
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
    syl
    eleq2d
    @96
    @19
    vw
    @8
    @13
    @30
    @8
    wceq
    #
    @32
    @16
    @95
    @18
    @98
    @31
    @15
    cX
    cc0
    @30
    @8
    fveq1
    eqeq1d
    @98
    @94
    @17
    cX
    @30
    @8
    clsw
    fveq2
    neeq1d
    anbi12d
    elrab
    syl6bb
    mpbird
    numclwwlk.r
    fmptd
end
