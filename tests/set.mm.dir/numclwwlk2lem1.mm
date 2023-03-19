include "cfrgr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "co.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "clsw.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "c2.mm"
include "caddc.mm"
include "wreu.mm"
include "crab.mm"
include "numclwwlkovq.mm"
include "3adant1.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "cpr.mm"
include "cedg.mm"
include "simpl1.mm"
include "wi.mm"
include "c1.mm"
include "cword.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wwlknp.mm"
include "peano2nn.mm"
include "adantl.mm"
include "simpl.mm"
include "jca.mm"
include "ex.mm"
include "3adant3.mm"
include "syl.mm"
include "lswlgt0cl.mm"
include "syl6.mm"
include "adantr.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "eleq1.mm"
include "biimprd.mm"
include "ad2antrl.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "neeq2.mm"
include "eqcoms.mm"
include "biimpa.mm"
include "3jca.mm"
include "frcond2.mm"
include "sylc.mm"
include "cclwwlkn.mm"
include "cmin.mm"
include "cn0.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "nnnn0.mm"
include "ad2antrr.mm"
include "wwlksext2clwwlk.mm"
include "sylan.mm"
include "cuz.mm"
include "cvv.mm"
include "wwlknbp.mm"
include "simp3d.mm"
include "cz.mm"
include "2z.mm"
include "nn0pzuz.mm"
include "sylancl.mm"
include "ad3antrrr.mm"
include "clwwlkext2edg.mm"
include "syl31anc.mm"
include "impbida.mm"
include "cvtx.mm"
include "syl6eleq.mm"
include "anim2i.mm"
include "simprd.mm"
include "numclwwlk2lem1lem.mm"
include "syl3anc.mm"
include "eqeq2.mm"
include "simpld.mm"
include "neeq2d.mm"
include "mpbird.mm"
include "nncn.mm"
include "2cnd.mm"
include "pncand.mm"
include "fveq2d.mm"
include "anbi2d.mm"
include "biantrud.mm"
include "2nn.mm"
include "nnaddcl.mm"
include "mpan2.mm"
include "numclwwlkovh.mm"
include "neeq12d.mm"
include "syl6rbb.mm"
include "3bitrd.mm"
include "reubidva.mm"
include "mpbid.mm"
include "sylbid.mm"

theorem numclwwlk2lem1
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )
  assume numclwwlk.h: |- H = ( v e. V , n e. NN |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) =/= ( w ` 0 ) ) } )

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
  disjoint W v
  disjoint W w
  disjoint G f
  disjoint f w
  disjoint K w
  disjoint N f
  disjoint V f
  disjoint X f
  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( ( G e. FriendGraph /\ X e. V /\ N e. NN ) -> ( W e. ( X Q N ) -> E! v e. V ( W ++ <" v "> ) e. ( X H ( N + 2 ) ) ) )

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
    cW
    cX
    cN
    cQ
    co
    #
    wcel
    #
    cW
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    cW
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
    cW
    vv
    cv
    #
    cs1
    cconcat
    co
    #
    cX
    cN
    c2
    caddc
    co
    #
    cH
    co
    #
    wcel
    #
    vv
    cV
    wreu
    #
    @3
    @5
    cW
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    @20
    clsw
    cfv
    #
    cX
    wne
    #
    wa
    #
    vw
    @6
    crab
    #
    wcel
    @13
    @3
    @4
    @26
    cW
    @1
    @2
    @4
    @26
    wceq
    @0
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
    3adant1
    eleq2d
    @25
    @12
    vw
    cW
    @6
    @20
    cW
    wceq
    #
    @22
    @9
    @24
    @11
    @27
    @21
    @8
    cX
    cc0
    @20
    cW
    fveq1
    eqeq1d
    @27
    @23
    @10
    cX
    @20
    cW
    clsw
    fveq2
    neeq1d
    anbi12d
    elrab
    syl6bb
    @3
    @13
    @19
    @3
    @13
    wa
    #
    @10
    @14
    cpr
    cG
    cedg
    cfv
    #
    wcel
    @14
    @8
    cpr
    @29
    wcel
    wa
    #
    vv
    cV
    wreu
    #
    @19
    @28
    @0
    @10
    cV
    wcel
    #
    @8
    cV
    wcel
    #
    @10
    @8
    wne
    #
    w3a
    @31
    @0
    @1
    @2
    @13
    simpl1
    @28
    @32
    @33
    @34
    @3
    @13
    @32
    @2
    @0
    @13
    @32
    wi
    @1
    @13
    @2
    @32
    @7
    @2
    @32
    wi
    @12
    @7
    @2
    cN
    c1
    caddc
    co
    #
    cn
    wcel
    #
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    @35
    wceq
    #
    wa
    #
    wa
    #
    @32
    @7
    @37
    @38
    vi
    cv
    #
    cW
    cfv
    @41
    c1
    caddc
    co
    cW
    cfv
    cpr
    @29
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    @2
    @40
    wi
    #
    vi
    @29
    cG
    cN
    cV
    cW
    numclwwlk.v
    @29
    eqid
    #
    wwlknp
    @37
    @38
    @43
    @42
    @39
    @2
    @40
    @39
    @2
    wa
    @36
    @39
    @2
    @36
    @39
    cN
    peano2nn
    adantl
    @39
    @2
    simpl
    jca
    ex
    3adant3
    syl
    @35
    cV
    cW
    lswlgt0cl
    syl6
    adantr
    com12
    3ad2ant3
    imp
    @3
    @13
    @33
    @1
    @0
    @13
    @33
    wi
    @2
    @13
    @1
    @33
    @9
    @1
    @33
    wi
    @7
    @11
    @9
    @33
    @1
    @8
    cX
    cV
    eleq1
    biimprd
    ad2antrl
    com12
    3ad2ant2
    imp
    @13
    @34
    @3
    @12
    @34
    @7
    @9
    @11
    @34
    @11
    @34
    wb
    cX
    @8
    cX
    @8
    @10
    neeq2
    eqcoms
    biimpa
    #
    adantl
    adantl
    3jca
    @10
    @8
    @29
    cG
    cV
    vv
    numclwwlk.v
    @44
    frcond2
    sylc
    @28
    @30
    @18
    vv
    cV
    @28
    @14
    cV
    wcel
    #
    wa
    #
    @30
    @15
    @16
    cG
    cclwwlkn
    co
    #
    wcel
    #
    @49
    cc0
    @15
    cfv
    #
    cX
    wceq
    #
    @16
    c2
    cmin
    co
    #
    @15
    cfv
    #
    @50
    wne
    #
    wa
    #
    wa
    #
    @18
    @47
    @30
    @49
    @47
    @7
    @46
    cN
    cn0
    wcel
    #
    w3a
    #
    @30
    @49
    @47
    @7
    @46
    @57
    @13
    @7
    @3
    @46
    @7
    @12
    simpl
    ad2antlr
    #
    @28
    @46
    simpr
    #
    @3
    @57
    @13
    @46
    @2
    @0
    @57
    @1
    cN
    nnnn0
    #
    3ad2ant3
    ad2antrr
    3jca
    @58
    @30
    @49
    @7
    @46
    @30
    @49
    wi
    @57
    @29
    cG
    cN
    cV
    cW
    @14
    numclwwlk.v
    @44
    wwlksext2clwwlk
    3adant3
    imp
    sylan
    @47
    @49
    wa
    @37
    @46
    @16
    c2
    cuz
    cfv
    wcel
    #
    @49
    @30
    @28
    @37
    @46
    @49
    @7
    @37
    @3
    @12
    @7
    cG
    cvv
    wcel
    @57
    @37
    cG
    cN
    cV
    cW
    numclwwlk.v
    wwlknbp
    simp3d
    ad2antrl
    ad2antrr
    @47
    @46
    @49
    @60
    adantr
    @3
    @62
    @13
    @46
    @49
    @2
    @0
    @62
    @1
    @2
    @57
    c2
    cz
    wcel
    @62
    @61
    2z
    cN
    c2
    nn0pzuz
    sylancl
    3ad2ant3
    ad3antrrr
    @47
    @49
    simpr
    @29
    cG
    @16
    cV
    cW
    @14
    numclwwlk.v
    @44
    clwwlkext2edg
    syl31anc
    impbida
    @47
    @55
    @49
    @47
    @55
    @51
    cN
    @15
    cfv
    #
    @50
    wne
    #
    wa
    #
    @47
    @65
    @50
    @8
    wceq
    #
    @63
    @8
    wne
    #
    wa
    #
    @47
    @14
    cG
    cvtx
    cfv
    #
    wcel
    @7
    @34
    @68
    @47
    @14
    cV
    @69
    @60
    numclwwlk.v
    syl6eleq
    @59
    @47
    @7
    @34
    @13
    @7
    @34
    wa
    @3
    @46
    @12
    @34
    @7
    @45
    anim2i
    ad2antlr
    simprd
    cG
    cN
    cW
    @14
    numclwwlk2lem1lem
    syl3anc
    #
    @47
    @51
    @66
    @64
    @67
    @13
    @51
    @66
    wb
    #
    @3
    @46
    @9
    @71
    @7
    @11
    @71
    cX
    @8
    cX
    @8
    @50
    eqeq2
    eqcoms
    ad2antrl
    ad2antlr
    @47
    @50
    @8
    @63
    @47
    @66
    @67
    @70
    simpld
    neeq2d
    anbi12d
    mpbird
    @47
    @54
    @64
    @51
    @47
    @53
    @63
    @50
    @47
    @52
    cN
    @15
    @3
    @52
    cN
    wceq
    #
    @13
    @46
    @2
    @0
    @72
    @1
    @2
    cN
    c2
    cN
    nncn
    @2
    2cnd
    pncand
    3ad2ant3
    ad2antrr
    fveq2d
    neeq1d
    anbi2d
    mpbird
    biantrud
    @47
    @18
    @15
    @22
    @52
    @20
    cfv
    #
    @21
    wne
    #
    wa
    #
    vw
    @48
    crab
    #
    wcel
    @56
    @47
    @17
    @76
    @15
    @47
    @1
    @16
    cn
    wcel
    #
    wa
    #
    @17
    @76
    wceq
    @3
    @78
    @13
    @46
    @1
    @2
    @78
    @0
    @2
    @77
    @1
    @2
    c2
    cn
    wcel
    @77
    2nn
    cN
    c2
    nnaddcl
    mpan2
    anim2i
    3adant1
    ad2antrr
    vw
    vv
    cQ
    vn
    cG
    cH
    @16
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlkovh
    syl
    eleq2d
    @75
    @55
    vw
    @15
    @48
    @20
    @15
    wceq
    #
    @22
    @51
    @74
    @54
    @79
    @21
    @50
    cX
    cc0
    @20
    @15
    fveq1
    #
    eqeq1d
    @79
    @73
    @53
    @21
    @50
    @52
    @20
    @15
    fveq1
    @80
    neeq12d
    anbi12d
    elrab
    syl6rbb
    3bitrd
    reubidva
    mpbid
    ex
    sylbid
end
