include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cmin.mm"
include "wo.mm"
include "simp3r.mm"
include "cmul.mm"
include "cz.mm"
include "nnz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "simp13.mm"
include "simp12.mm"
include "nnaddcld.mm"
include "nnzd.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simprd.mm"
include "breq1.mm"
include "biimpd.mm"
include "mpan9.mm"
include "wi.mm"
include "simpl13.mm"
include "simpl12.mm"
include "zaddcld.mm"
include "zsubcld.mm"
include "2z.mm"
include "dvdsmultr1.mm"
include "mp3an1.mm"
include "mpd.mm"
include "cc.mm"
include "nncnd.mm"
include "subsq.mm"
include "breqtrrd.mm"
include "simpl2.mm"
include "oveq1d.mm"
include "simpl11.mm"
include "nnsqcld.mm"
include "pncand.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "wb.mm"
include "adantr.mm"
include "cprime.mm"
include "2prm.mm"
include "2nn.mm"
include "prmdvdsexp.mm"
include "mp3an13.mm"
include "syl.mm"
include "mpbid.mm"
include "mtand.mm"
include "cneg.mm"
include "neg1z.mm"
include "gcdaddm.mm"
include "pnncan.mm"
include "3anidm23.mm"
include "subcl.mm"
include "mulm1d.mm"
include "oveq2d.mm"
include "addcl.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "2times.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "eqbrtrd.mm"
include "1z.mm"
include "ppncan.mm"
include "3anidm13.mm"
include "mulid2d.mm"
include "cc0.mm"
include "wne.mm"
include "nnaddcl.mm"
include "nnne0d.mm"
include "ancoms.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "dvdsgcd.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "cn0.mm"
include "2nn0.mm"
include "mulgcd.mm"
include "pythagtriplem3.mm"
include "2t1e2.mm"
include "syl6eq.mm"
include "dvdsprime.mm"
include "orel1.mm"
include "sylc.mm"

theorem pythagtriplem4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( ( C - B ) gcd ( C + B ) ) = 1 )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    #
    c2
    cA
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cC
    cB
    cmin
    co
    #
    cC
    cB
    caddc
    co
    #
    cgcd
    co
    #
    c2
    wceq
    #
    wn
    @17
    @16
    c1
    wceq
    #
    wo
    #
    @18
    @13
    @17
    @10
    @3
    @8
    @9
    @11
    simp3r
    @13
    @17
    wa
    #
    c2
    @4
    cdvds
    wbr
    #
    @10
    @20
    c2
    @7
    @5
    cmin
    co
    #
    @4
    cdvds
    @20
    c2
    @15
    @14
    cmul
    co
    #
    @22
    cdvds
    @20
    c2
    @15
    cdvds
    wbr
    #
    c2
    @23
    cdvds
    wbr
    #
    @13
    @16
    @15
    cdvds
    wbr
    #
    @17
    @24
    @13
    @16
    @14
    cdvds
    wbr
    #
    @26
    @13
    @14
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @27
    @26
    wa
    @3
    @8
    @28
    @12
    @1
    @2
    @28
    @0
    @2
    cC
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    @28
    @1
    cC
    nnz
    cB
    nnz
    cC
    cB
    zsubcl
    syl2anr
    3adant1
    3ad2ant1
    #
    @13
    @15
    @13
    cC
    cB
    @0
    @1
    @2
    @8
    @12
    simp13
    #
    @0
    @1
    @2
    @8
    @12
    simp12
    #
    nnaddcld
    nnzd
    #
    @14
    @15
    gcddvds
    syl2anc
    simprd
    @17
    @26
    @24
    @16
    c2
    @15
    cdvds
    breq1
    biimpd
    mpan9
    @20
    @29
    @28
    @24
    @25
    wi
    #
    @20
    cC
    cB
    @20
    cC
    @0
    @1
    @2
    @8
    @12
    @17
    simpl13
    #
    nnzd
    #
    @20
    cB
    @0
    @1
    @2
    @8
    @12
    @17
    simpl12
    #
    nnzd
    #
    zaddcld
    @20
    cC
    cB
    @38
    @40
    zsubcld
    c2
    cz
    wcel
    #
    @29
    @28
    @36
    2z
    c2
    @15
    @14
    dvdsmultr1
    mp3an1
    syl2anc
    mpd
    @20
    cC
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @22
    @23
    wceq
    @20
    cC
    @37
    nncnd
    @20
    cB
    @39
    nncnd
    cC
    cB
    subsq
    syl2anc
    breqtrrd
    @20
    @6
    @5
    cmin
    co
    @22
    @4
    @20
    @6
    @7
    @5
    cmin
    @3
    @8
    @12
    @17
    simpl2
    oveq1d
    @20
    @4
    @5
    @20
    @4
    @20
    cA
    @0
    @1
    @2
    @8
    @12
    @17
    simpl11
    nnsqcld
    nncnd
    @20
    @5
    @20
    cB
    @39
    nnsqcld
    nncnd
    pncand
    eqtr3d
    breqtrd
    @20
    cA
    cz
    wcel
    #
    @21
    @10
    wb
    #
    @13
    @44
    @17
    @3
    @8
    @44
    @12
    @0
    @1
    @44
    @2
    cA
    nnz
    3ad2ant1
    3ad2ant1
    adantr
    c2
    cprime
    wcel
    #
    @44
    c2
    cn
    wcel
    @45
    2prm
    2nn
    cA
    c2
    c2
    prmdvdsexp
    mp3an13
    syl
    mpbid
    mtand
    @13
    @16
    c2
    cdvds
    wbr
    #
    @19
    @13
    @16
    c2
    cB
    cmul
    co
    #
    c2
    cC
    cmul
    co
    #
    cgcd
    co
    #
    c2
    cdvds
    @13
    @16
    @48
    cdvds
    wbr
    #
    @16
    @49
    cdvds
    wbr
    #
    @16
    @50
    cdvds
    wbr
    #
    @13
    @16
    @14
    @48
    cgcd
    co
    #
    @48
    cdvds
    @13
    @16
    @14
    @15
    c1
    cneg
    #
    @14
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    @54
    @13
    @28
    @29
    @16
    @58
    wceq
    #
    @32
    @35
    @55
    cz
    wcel
    @28
    @29
    @59
    neg1z
    @55
    @14
    @15
    gcdaddm
    mp3an1
    syl2anc
    @13
    @42
    @43
    @58
    @54
    wceq
    @13
    cC
    @33
    nncnd
    #
    @13
    cB
    @34
    nncnd
    #
    @42
    @43
    wa
    #
    @57
    @48
    @14
    cgcd
    @62
    @15
    @14
    cmin
    co
    #
    cB
    cB
    caddc
    co
    #
    @57
    @48
    @42
    @43
    @63
    @64
    wceq
    cC
    cB
    cB
    pnncan
    3anidm23
    @62
    @57
    @15
    @14
    cneg
    #
    caddc
    co
    @63
    @62
    @56
    @65
    @15
    caddc
    @62
    @14
    cC
    cB
    subcl
    #
    mulm1d
    oveq2d
    @62
    @15
    @14
    cC
    cB
    addcl
    @66
    negsubd
    eqtrd
    @43
    @48
    @64
    wceq
    @42
    cB
    2times
    adantl
    3eqtr4d
    oveq2d
    syl2anc
    eqtrd
    @13
    @54
    @14
    cdvds
    wbr
    #
    @54
    @48
    cdvds
    wbr
    #
    @13
    @28
    @48
    cz
    wcel
    #
    @67
    @68
    wa
    @32
    @13
    @41
    @31
    @69
    2z
    @13
    cB
    @34
    nnzd
    #
    c2
    cB
    zmulcl
    sylancr
    #
    @14
    @48
    gcddvds
    syl2anc
    simprd
    eqbrtrd
    @13
    @16
    @14
    @49
    cgcd
    co
    #
    @49
    cdvds
    @13
    @16
    @14
    @15
    c1
    @14
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    @72
    @13
    @28
    @29
    @16
    @75
    wceq
    #
    @32
    @35
    c1
    cz
    wcel
    @28
    @29
    @76
    1z
    c1
    @14
    @15
    gcdaddm
    mp3an1
    syl2anc
    @13
    @74
    @49
    @14
    cgcd
    @13
    @42
    @43
    @74
    @49
    wceq
    @60
    @61
    @62
    @15
    @14
    caddc
    co
    #
    cC
    cC
    caddc
    co
    #
    @74
    @49
    @42
    @43
    @77
    @78
    wceq
    cC
    cB
    cC
    ppncan
    3anidm13
    @62
    @73
    @14
    @15
    caddc
    @62
    @14
    @66
    mulid2d
    oveq2d
    @42
    @49
    @78
    wceq
    @43
    cC
    2times
    adantr
    3eqtr4d
    syl2anc
    oveq2d
    eqtrd
    @13
    @72
    @14
    cdvds
    wbr
    #
    @72
    @49
    cdvds
    wbr
    #
    @13
    @28
    @49
    cz
    wcel
    #
    @79
    @80
    wa
    @32
    @13
    @41
    @30
    @81
    2z
    @13
    cC
    @33
    nnzd
    #
    c2
    cC
    zmulcl
    sylancr
    #
    @14
    @49
    gcddvds
    syl2anc
    simprd
    eqbrtrd
    @13
    @16
    cz
    wcel
    @69
    @81
    @51
    @52
    wa
    @53
    wi
    @13
    @16
    @13
    @28
    @29
    @14
    cc0
    wceq
    #
    @15
    cc0
    wceq
    #
    wa
    wn
    @16
    cn
    wcel
    #
    @32
    @35
    @13
    @85
    @84
    @13
    @15
    cc0
    @3
    @8
    @15
    cc0
    wne
    #
    @12
    @1
    @2
    @87
    @0
    @2
    @1
    @87
    @2
    @1
    wa
    @15
    cC
    cB
    nnaddcl
    nnne0d
    ancoms
    3adant1
    3ad2ant1
    neneqd
    intnand
    @14
    @15
    gcdn0cl
    syl21anc
    #
    nnzd
    @71
    @83
    @16
    @48
    @49
    dvdsgcd
    syl3anc
    mp2and
    @13
    @50
    c2
    cB
    cC
    cgcd
    co
    #
    cmul
    co
    #
    c2
    @13
    @31
    @30
    @50
    @90
    wceq
    #
    @70
    @82
    c2
    cn0
    wcel
    @31
    @30
    @91
    2nn0
    c2
    cB
    cC
    mulgcd
    mp3an1
    syl2anc
    @13
    @90
    c2
    c1
    cmul
    co
    c2
    @13
    @89
    c1
    c2
    cmul
    cA
    cB
    cC
    pythagtriplem3
    oveq2d
    2t1e2
    syl6eq
    eqtrd
    breqtrd
    @13
    @46
    @86
    @47
    @19
    wb
    2prm
    @88
    c2
    @16
    dvdsprime
    sylancr
    mpbid
    @17
    @18
    orel1
    sylc
end
