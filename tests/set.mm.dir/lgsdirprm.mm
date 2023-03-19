include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "clgs.mm"
include "wceq.mm"
include "c2.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "lgsdir2.mm"
include "syl2anc.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "zmulcld.mm"
include "simpl3.mm"
include "prmz.mm"
include "syl.mm"
include "lgscl.mm"
include "zcnd.mm"
include "cmin.mm"
include "subcld.mm"
include "cabs.mm"
include "cfv.mm"
include "cmo.mm"
include "cc0.mm"
include "cr.mm"
include "crp.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "abscld.mm"
include "cn.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "absge0d.mm"
include "2re.mm"
include "a1i.mm"
include "nnred.mm"
include "caddc.mm"
include "readdcld.mm"
include "abs2dif2d.mm"
include "c1.mm"
include "1red.mm"
include "lgsle1.mm"
include "cv.mm"
include "crab.mm"
include "eqid.mm"
include "lgscl2.mm"
include "lgslem3.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "simprbi.mm"
include "le2addd.mm"
include "df-2.mm"
include "syl6breqr.mm"
include "letrd.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "3syl.mm"
include "wb.mm"
include "ltlen.mm"
include "sylancr.mm"
include "mpbir2and.mm"
include "lelttrd.mm"
include "modid.mm"
include "syl22anc.mm"
include "cdvds.mm"
include "cdiv.mm"
include "cexp.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "mulexpd.mm"
include "cn0.mm"
include "zexpcl.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "lgsvalmod.mm"
include "zred.mm"
include "modmul1.mm"
include "syl221anc.mm"
include "3eqtrd.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "zsubcld.mm"
include "dvdsabsb.mm"
include "dvdsmod0.mm"
include "eqtr3d.mm"
include "abs00d.mm"
include "subeq0d.mm"
include "pm2.61dane.mm"

theorem lgsdirprm
  let cA: class A
  let cB: class B
  let cP: class P
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cM: class M
  let wph: wff ph
  let vp: setvar p
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ P e. Prime ) -> ( ( A x. B ) /L P ) = ( ( A /L P ) x. ( B /L P ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
    cP
    clgs
    co
    #
    cA
    cP
    clgs
    co
    #
    cB
    cP
    clgs
    co
    #
    cmul
    co
    #
    wceq
    cP
    c2
    @3
    cP
    c2
    wceq
    #
    wa
    #
    @4
    c2
    clgs
    co
    #
    cA
    c2
    clgs
    co
    #
    cB
    c2
    clgs
    co
    #
    cmul
    co
    #
    @5
    @8
    @10
    @0
    @1
    @11
    @14
    wceq
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    cA
    cB
    lgsdir2
    syl2anc
    @10
    cP
    c2
    @4
    clgs
    @3
    @9
    simpr
    #
    oveq2d
    @10
    @6
    @12
    @7
    @13
    cmul
    @10
    cP
    c2
    cA
    clgs
    @15
    oveq2d
    @10
    cP
    c2
    cB
    clgs
    @15
    oveq2d
    oveq12d
    3eqtr4d
    @3
    cP
    c2
    wne
    #
    wa
    #
    @5
    @8
    @17
    @5
    @17
    @4
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @17
    cA
    cB
    @0
    @1
    @2
    @16
    simpl1
    #
    @0
    @1
    @2
    @16
    simpl2
    #
    zmulcld
    #
    @17
    @2
    @19
    @0
    @1
    @2
    @16
    simpl3
    #
    cP
    prmz
    syl
    #
    @4
    cP
    lgscl
    syl2anc
    #
    zcnd
    #
    @17
    @8
    @17
    @6
    @7
    @17
    @0
    @19
    @6
    cz
    wcel
    @21
    @25
    cA
    cP
    lgscl
    syl2anc
    #
    @17
    @1
    @19
    @7
    cz
    wcel
    #
    @22
    @25
    cB
    cP
    lgscl
    syl2anc
    #
    zmulcld
    #
    zcnd
    #
    @17
    @5
    @8
    cmin
    co
    #
    @17
    @5
    @8
    @27
    @32
    subcld
    #
    @17
    @33
    cabs
    cfv
    #
    cP
    cmo
    co
    #
    @35
    cc0
    @17
    @35
    cr
    wcel
    cP
    crp
    wcel
    #
    cc0
    @35
    cle
    wbr
    @35
    cP
    clt
    wbr
    @36
    @35
    wceq
    @17
    @33
    @34
    abscld
    #
    @17
    cP
    @17
    @2
    cP
    cn
    wcel
    #
    @24
    cP
    prmnn
    syl
    #
    nnrpd
    #
    @17
    @33
    @34
    absge0d
    @17
    @35
    c2
    cP
    @38
    c2
    cr
    wcel
    #
    @17
    2re
    a1i
    #
    @17
    cP
    @40
    nnred
    #
    @17
    @35
    @5
    cabs
    cfv
    #
    @8
    cabs
    cfv
    #
    caddc
    co
    #
    c2
    @38
    @17
    @45
    @46
    @17
    @5
    @27
    abscld
    #
    @17
    @8
    @32
    abscld
    #
    readdcld
    @43
    @17
    @5
    @8
    @27
    @32
    abs2dif2d
    @17
    @47
    c1
    c1
    caddc
    co
    c2
    cle
    @17
    @45
    @46
    c1
    c1
    @48
    @49
    @17
    1red
    #
    @50
    @17
    @18
    @19
    @45
    c1
    cle
    wbr
    @23
    @25
    @4
    cP
    lgsle1
    syl2anc
    @17
    @8
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cz
    crab
    #
    wcel
    #
    @46
    c1
    cle
    wbr
    #
    @17
    @6
    @54
    wcel
    #
    @7
    @54
    wcel
    #
    @55
    @17
    @0
    @19
    @57
    @21
    @25
    vx
    cA
    cP
    @54
    @54
    eqid
    #
    lgscl2
    syl2anc
    @17
    @1
    @19
    @58
    @22
    @25
    vx
    cB
    cP
    @54
    @59
    lgscl2
    syl2anc
    vx
    @6
    @7
    @54
    @59
    lgslem3
    syl2anc
    @55
    @8
    cz
    wcel
    #
    @56
    @53
    @56
    vx
    @8
    cz
    @51
    @8
    wceq
    @52
    @46
    c1
    cle
    @51
    @8
    cabs
    fveq2
    breq1d
    elrab
    simprbi
    syl
    le2addd
    df-2
    syl6breqr
    letrd
    @17
    c2
    cP
    clt
    wbr
    #
    c2
    cP
    cle
    wbr
    #
    @16
    @17
    @2
    cP
    c2
    cuz
    cfv
    wcel
    @62
    @24
    cP
    prmuz2
    c2
    cP
    eluzle
    3syl
    @3
    @16
    simpr
    #
    @17
    @42
    cP
    cr
    wcel
    @61
    @62
    @16
    wa
    wb
    2re
    @44
    c2
    cP
    ltlen
    sylancr
    mpbir2and
    lelttrd
    @35
    cP
    modid
    syl22anc
    @17
    @39
    cP
    @35
    cdvds
    wbr
    #
    @36
    cc0
    wceq
    @40
    @17
    cP
    @33
    cdvds
    wbr
    #
    @64
    @17
    @5
    cP
    cmo
    co
    #
    @8
    cP
    cmo
    co
    #
    wceq
    #
    @65
    @17
    @4
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    cB
    @69
    cexp
    co
    #
    cA
    @69
    cexp
    co
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    @66
    @67
    @17
    @70
    @74
    cP
    cmo
    @17
    @70
    @73
    @72
    cmul
    co
    @74
    @17
    cA
    cB
    @69
    @17
    cA
    @21
    zcnd
    @17
    cB
    @22
    zcnd
    @17
    @69
    @17
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @69
    cn
    wcel
    @17
    @2
    @16
    @76
    @24
    @63
    cP
    cprime
    c2
    eldifsn
    sylanbrc
    #
    cP
    oddprm
    syl
    nnnn0d
    #
    mulexpd
    @17
    @73
    @72
    @17
    @73
    @17
    @0
    @69
    cn0
    wcel
    #
    @73
    cz
    wcel
    #
    @21
    @78
    cA
    @69
    zexpcl
    syl2anc
    #
    zcnd
    #
    @17
    @72
    @17
    @1
    @79
    @72
    cz
    wcel
    @22
    @78
    cB
    @69
    zexpcl
    syl2anc
    #
    zcnd
    mulcomd
    eqtrd
    oveq1d
    @17
    @18
    @76
    @66
    @71
    wceq
    @23
    @77
    @4
    cP
    lgsvalmod
    syl2anc
    @17
    @67
    @73
    @7
    cmul
    co
    #
    cP
    cmo
    co
    #
    @7
    @73
    cmul
    co
    #
    cP
    cmo
    co
    #
    @75
    @17
    @6
    cr
    wcel
    @73
    cr
    wcel
    @29
    @37
    @6
    cP
    cmo
    co
    @73
    cP
    cmo
    co
    wceq
    #
    @67
    @85
    wceq
    @17
    @6
    @28
    zred
    @17
    @73
    @81
    zred
    @30
    @41
    @17
    @0
    @76
    @88
    @21
    @77
    cA
    cP
    lgsvalmod
    syl2anc
    @6
    @73
    @7
    cP
    modmul1
    syl221anc
    @17
    @84
    @86
    cP
    cmo
    @17
    @73
    @7
    @82
    @17
    @7
    @30
    zcnd
    mulcomd
    oveq1d
    @17
    @7
    cr
    wcel
    @72
    cr
    wcel
    @80
    @37
    @7
    cP
    cmo
    co
    @72
    cP
    cmo
    co
    wceq
    #
    @87
    @75
    wceq
    @17
    @7
    @30
    zred
    @17
    @72
    @83
    zred
    @81
    @41
    @17
    @1
    @76
    @89
    @22
    @77
    cB
    cP
    lgsvalmod
    syl2anc
    @7
    @72
    @73
    cP
    modmul1
    syl221anc
    3eqtrd
    3eqtr4d
    @17
    @39
    @20
    @60
    @68
    @65
    wb
    @40
    @26
    @31
    @5
    @8
    cP
    moddvds
    syl3anc
    mpbid
    @17
    @19
    @33
    cz
    wcel
    @65
    @64
    wb
    @25
    @17
    @5
    @8
    @26
    @31
    zsubcld
    cP
    @33
    dvdsabsb
    syl2anc
    mpbid
    cP
    @35
    dvdsmod0
    syl2anc
    eqtr3d
    abs00d
    subeq0d
    pm2.61dane
end
