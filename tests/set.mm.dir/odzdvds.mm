include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cn0.mm"
include "wa.mm"
include "codz.mm"
include "cfv.mm"
include "cmo.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "wn.mm"
include "wi.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "nn0re.mm"
include "adantl.mm"
include "odzcl.mm"
include "adantr.mm"
include "nnrpd.mm"
include "modlt.mm"
include "syl2anc.mm"
include "nn0z.mm"
include "zmodcld.mm"
include "nn0red.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "cv.mm"
include "crab.mm"
include "cinf.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "elrab.mm"
include "cuz.mm"
include "wss.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "infssuzle.mm"
include "mpan.mm"
include "sylbir.mm"
include "ancoms.mm"
include "odzval.mm"
include "breq1d.mm"
include "syl5ibr.mm"
include "mtod.mm"
include "imnan.mm"
include "sylibr.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "syld.mm"
include "simpl1.mm"
include "nnzd.mm"
include "dvds0.mm"
include "syl.mm"
include "simpl2.mm"
include "zcnd.mm"
include "exp0d.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "nnnn0d.mm"
include "nndivred.mm"
include "nn0ge0.mm"
include "wb.mm"
include "nngt0d.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "flge0nn0.mm"
include "nn0mulcld.mm"
include "zexpcl.mm"
include "zred.mm"
include "1red.mm"
include "expmuld.mm"
include "1zzd.mm"
include "odzid.mm"
include "moddvds.mm"
include "mpbird.mm"
include "modexp.mm"
include "syl221anc.mm"
include "flcld.mm"
include "1exp.mm"
include "3eqtrd.mm"
include "modmul1.mm"
include "caddc.mm"
include "expaddd.mm"
include "modval.mm"
include "oveq2d.mm"
include "nn0cnd.mm"
include "recnd.mm"
include "pncan3d.mm"
include "eqtrd.mm"
include "eqtr3d.mm"
include "mulid2d.mm"
include "3eqtr3d.mm"
include "eqeq1d.mm"
include "sylancom.mm"
include "3bitr3d.mm"
include "dvdsval3.mm"
include "3bitr4d.mm"

theorem odzdvds
  let cA: class A
  let cK: class K
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) /\ K e. NN0 ) -> ( N || ( ( A ^ K ) - 1 ) <-> ( ( odZ ` N ) ` A ) || K ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cN
    cA
    cK
    cA
    cN
    codz
    cfv
    cfv
    #
    cmo
    co
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    @7
    cc0
    wceq
    #
    cN
    cA
    cK
    cexp
    co
    #
    c1
    cmin
    co
    cdvds
    wbr
    #
    @6
    cK
    cdvds
    wbr
    #
    @5
    @10
    @11
    @5
    @10
    @7
    cn
    wcel
    #
    wn
    #
    @11
    @5
    @10
    @15
    wa
    #
    wn
    @10
    @16
    wi
    @5
    @17
    @6
    @7
    cle
    wbr
    #
    @5
    @7
    @6
    clt
    wbr
    #
    @18
    wn
    @5
    cK
    cr
    wcel
    #
    @6
    crp
    wcel
    #
    @19
    @4
    @20
    @3
    cK
    nn0re
    adantl
    #
    @5
    @6
    @3
    @6
    cn
    wcel
    #
    @4
    cA
    cN
    odzcl
    adantr
    #
    nnrpd
    #
    cK
    @6
    modlt
    syl2anc
    @5
    @7
    @6
    @5
    @7
    @5
    cK
    @6
    @4
    cK
    cz
    wcel
    #
    @3
    cK
    nn0z
    adantl
    #
    @24
    zmodcld
    #
    nn0red
    @5
    @6
    @24
    nnred
    #
    ltnled
    mpbid
    @17
    @18
    @5
    cN
    cA
    vn
    cv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    @7
    cle
    wbr
    #
    @15
    @10
    @36
    @15
    @10
    wa
    @7
    @34
    wcel
    #
    @36
    @33
    @10
    vn
    @7
    cn
    @30
    @7
    wceq
    #
    @32
    @9
    cN
    cdvds
    @38
    @31
    @8
    c1
    cmin
    @30
    @7
    cA
    cexp
    oveq2
    oveq1d
    breq2d
    elrab
    @34
    c1
    cuz
    cfv
    #
    wss
    @37
    @36
    @34
    cn
    @39
    @33
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    @7
    @34
    c1
    infssuzle
    mpan
    sylbir
    ancoms
    @5
    @6
    @35
    @7
    cle
    @3
    @6
    @35
    wceq
    @4
    cA
    vn
    cN
    odzval
    adantr
    breq1d
    syl5ibr
    mtod
    @10
    @15
    imnan
    sylibr
    @5
    @15
    @11
    @5
    @7
    cn0
    wcel
    #
    @15
    @11
    wo
    @28
    @7
    elnn0
    sylib
    ord
    syld
    @5
    @10
    @11
    cN
    cA
    cc0
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    @5
    cN
    cc0
    @42
    cdvds
    @5
    cN
    cz
    wcel
    cN
    cc0
    cdvds
    wbr
    @5
    cN
    @0
    @1
    @2
    @4
    simpl1
    #
    nnzd
    cN
    dvds0
    syl
    @5
    @42
    c1
    c1
    cmin
    co
    cc0
    @5
    @41
    c1
    c1
    cmin
    @5
    cA
    @5
    cA
    @0
    @1
    @2
    @4
    simpl2
    #
    zcnd
    #
    exp0d
    oveq1d
    1m1e0
    syl6eq
    breqtrrd
    @11
    @9
    @42
    cN
    cdvds
    @11
    @8
    @41
    c1
    cmin
    @7
    cc0
    cA
    cexp
    oveq2
    oveq1d
    breq2d
    syl5ibrcom
    impbid
    @5
    @12
    cN
    cmo
    co
    #
    c1
    cN
    cmo
    co
    #
    wceq
    #
    @8
    cN
    cmo
    co
    #
    @47
    wceq
    #
    @13
    @10
    @5
    @46
    @49
    @47
    @5
    cA
    @6
    cK
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cexp
    co
    #
    @8
    cmul
    co
    #
    cN
    cmo
    co
    #
    c1
    @8
    cmul
    co
    #
    cN
    cmo
    co
    #
    @46
    @49
    @5
    @54
    cr
    wcel
    c1
    cr
    wcel
    @8
    cz
    wcel
    #
    cN
    crp
    wcel
    #
    @54
    cN
    cmo
    co
    #
    @47
    wceq
    @56
    @58
    wceq
    @5
    @54
    @5
    @1
    @53
    cn0
    wcel
    @54
    cz
    wcel
    @44
    @5
    @6
    @52
    @5
    @6
    @24
    nnnn0d
    #
    @5
    @51
    cr
    wcel
    cc0
    @51
    cle
    wbr
    #
    @52
    cn0
    wcel
    #
    @5
    cK
    @6
    @22
    @24
    nndivred
    #
    @5
    cc0
    cK
    cle
    wbr
    #
    @63
    @4
    @66
    @3
    cK
    nn0ge0
    adantl
    @5
    @20
    @6
    cr
    wcel
    cc0
    @6
    clt
    wbr
    @66
    @63
    wb
    @22
    @29
    @5
    @6
    @24
    nngt0d
    cK
    @6
    ge0div
    syl3anc
    mpbid
    @51
    flge0nn0
    syl2anc
    #
    nn0mulcld
    #
    cA
    @53
    zexpcl
    syl2anc
    zred
    @5
    1red
    @5
    @1
    @40
    @59
    @44
    @28
    cA
    @7
    zexpcl
    syl2anc
    #
    @5
    cN
    @43
    nnrpd
    #
    @5
    @61
    cA
    @6
    cexp
    co
    #
    @52
    cexp
    co
    #
    cN
    cmo
    co
    #
    c1
    @52
    cexp
    co
    #
    cN
    cmo
    co
    #
    @47
    @5
    @54
    @72
    cN
    cmo
    @5
    cA
    @6
    @52
    @45
    @67
    @62
    expmuld
    oveq1d
    @5
    @71
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @64
    @60
    @71
    cN
    cmo
    co
    @47
    wceq
    #
    @73
    @75
    wceq
    @5
    @1
    @6
    cn0
    wcel
    @76
    @44
    @62
    cA
    @6
    zexpcl
    syl2anc
    #
    @5
    1zzd
    #
    @67
    @70
    @5
    @78
    cN
    @71
    c1
    cmin
    co
    cdvds
    wbr
    #
    @3
    @81
    @4
    cA
    cN
    odzid
    adantr
    @5
    @0
    @76
    @77
    @78
    @81
    wb
    @43
    @79
    @80
    @71
    c1
    cN
    moddvds
    syl3anc
    mpbird
    @71
    c1
    @52
    cN
    modexp
    syl221anc
    @5
    @74
    c1
    cN
    cmo
    @5
    @52
    cz
    wcel
    @74
    c1
    wceq
    @5
    @51
    @65
    flcld
    @52
    1exp
    syl
    oveq1d
    3eqtrd
    @54
    c1
    @8
    cN
    modmul1
    syl221anc
    @5
    @55
    @12
    cN
    cmo
    @5
    cA
    @53
    @7
    caddc
    co
    #
    cexp
    co
    @55
    @12
    @5
    cA
    @53
    @7
    @45
    @28
    @68
    expaddd
    @5
    @82
    cK
    cA
    cexp
    @5
    @82
    @53
    cK
    @53
    cmin
    co
    #
    caddc
    co
    cK
    @5
    @7
    @83
    @53
    caddc
    @5
    @20
    @21
    @7
    @83
    wceq
    @22
    @25
    cK
    @6
    modval
    syl2anc
    oveq2d
    @5
    @53
    cK
    @5
    @53
    @68
    nn0cnd
    @5
    cK
    @22
    recnd
    pncan3d
    eqtrd
    oveq2d
    eqtr3d
    oveq1d
    @5
    @57
    @8
    cN
    cmo
    @5
    @8
    @5
    @8
    @69
    zcnd
    mulid2d
    oveq1d
    3eqtr3d
    eqeq1d
    @5
    @0
    @12
    cz
    wcel
    #
    @77
    @48
    @13
    wb
    @43
    @3
    @4
    @1
    @84
    @44
    cA
    cK
    zexpcl
    sylancom
    @80
    @12
    c1
    cN
    moddvds
    syl3anc
    @5
    @0
    @59
    @77
    @50
    @10
    wb
    @43
    @69
    @80
    @8
    c1
    cN
    moddvds
    syl3anc
    3bitr3d
    @5
    @23
    @26
    @14
    @11
    wb
    @24
    @27
    @6
    cK
    dvdsval3
    syl2anc
    3bitr4d
end
