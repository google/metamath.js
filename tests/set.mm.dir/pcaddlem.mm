include "caddc.mm"
include "co.mm"
include "cpc.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "eluzel2.mm"
include "syl.mm"
include "zred.mm"
include "adantr.mm"
include "cprime.mm"
include "cn.mm"
include "prmnn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "eluzelz.mm"
include "zsubcld.mm"
include "expclzd.mm"
include "cdvds.mm"
include "wn.mm"
include "simpld.mm"
include "zcnd.mm"
include "divassd.mm"
include "oveq2d.mm"
include "mulcld.mm"
include "divadddivd.mm"
include "eqtr3d.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "uznn0sub.mm"
include "nnexpcld.mm"
include "zaddcld.mm"
include "mul01d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "divcld.mm"
include "adddid.mm"
include "pncan3d.mm"
include "cc.mm"
include "expaddz.mm"
include "syl22anc.mm"
include "oveq1d.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "neeq1d.mm"
include "3imtr3d.mm"
include "nnmulcld.mm"
include "div0d.mm"
include "oveq1.mm"
include "syld.mm"
include "imp.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "pcmul.mm"
include "syl122anc.mm"
include "simprd.mm"
include "wb.mm"
include "pceq0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "00id.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "eqeltrd.mm"
include "nn0addge1.mm"
include "cq.mm"
include "nnq.mm"
include "qexpclz.mm"
include "syl3anc.mm"
include "expne0d.mm"
include "znq.mm"
include "qmulcl.mm"
include "qaddcl.mm"
include "sylbird.mm"
include "pcqmul.mm"
include "pcid.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"
include "cpnf.mm"
include "cxr.mm"
include "rexrd.mm"
include "pnfge.mm"
include "pc0.mm"
include "pm2.61ne.mm"

theorem pcaddlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cM: class M
  let cN: class N
  assume pcaddlem.1: |- ( ph -> P e. Prime )
  assume pcaddlem.2: |- ( ph -> A = ( ( P ^ M ) x. ( R / S ) ) )
  assume pcaddlem.3: |- ( ph -> B = ( ( P ^ N ) x. ( T / U ) ) )
  assume pcaddlem.4: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume pcaddlem.5: |- ( ph -> ( R e. ZZ /\ -. P || R ) )
  assume pcaddlem.6: |- ( ph -> ( S e. NN /\ -. P || S ) )
  assume pcaddlem.7: |- ( ph -> ( T e. ZZ /\ -. P || T ) )
  assume pcaddlem.8: |- ( ph -> ( U e. NN /\ -. P || U ) )


  assert |- ( ph -> M <_ ( P pCnt ( A + B ) ) )

  proof
    wph
    cM
    cP
    cA
    cB
    caddc
    co
    #
    cpc
    co
    #
    cle
    wbr
    cM
    cP
    cc0
    cpc
    co
    #
    cle
    wbr
    @0
    cc0
    @0
    cc0
    wceq
    @1
    @2
    cM
    cle
    @0
    cc0
    cP
    cpc
    oveq2
    breq2d
    wph
    @0
    cc0
    wne
    #
    wa
    #
    cM
    cM
    cP
    cR
    cS
    cdiv
    co
    #
    cP
    cN
    cM
    cmin
    co
    #
    cexp
    co
    #
    cT
    cU
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cpc
    co
    #
    caddc
    co
    #
    @1
    cle
    @4
    cM
    cr
    wcel
    #
    @11
    cn0
    wcel
    cM
    @12
    cle
    wbr
    wph
    @13
    @3
    wph
    cM
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    pcaddlem.4
    cM
    cN
    eluzel2
    syl
    #
    zred
    #
    adantr
    @4
    @11
    cP
    cR
    cU
    cmul
    co
    #
    @7
    cT
    cmul
    co
    #
    cS
    cmul
    co
    #
    caddc
    co
    #
    cpc
    co
    #
    cn0
    @4
    @11
    cP
    @21
    cS
    cU
    cmul
    co
    #
    cdiv
    co
    #
    cpc
    co
    #
    @22
    cP
    @23
    cpc
    co
    #
    cmin
    co
    #
    @22
    wph
    @11
    @25
    wceq
    @3
    wph
    @10
    @24
    cP
    cpc
    wph
    @5
    @19
    cU
    cdiv
    co
    #
    caddc
    co
    @10
    @24
    wph
    @28
    @9
    @5
    caddc
    wph
    @7
    cT
    cU
    wph
    cP
    @6
    wph
    cP
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    pcaddlem.1
    cP
    prmnn
    syl
    #
    nncnd
    #
    wph
    cP
    @31
    nnne0d
    #
    wph
    cN
    cM
    wph
    @14
    cN
    cz
    wcel
    pcaddlem.4
    cM
    cN
    eluzelz
    syl
    #
    @16
    zsubcld
    #
    expclzd
    #
    wph
    cT
    wph
    cT
    cz
    wcel
    #
    cP
    cT
    cdvds
    wbr
    wn
    pcaddlem.7
    simpld
    #
    zcnd
    #
    wph
    cU
    wph
    cU
    cn
    wcel
    #
    cP
    cU
    cdvds
    wbr
    wn
    #
    pcaddlem.8
    simpld
    #
    nncnd
    #
    wph
    cU
    @42
    nnne0d
    #
    divassd
    oveq2d
    wph
    cR
    cS
    @19
    cU
    wph
    cR
    wph
    cR
    cz
    wcel
    #
    cP
    cR
    cdvds
    wbr
    wn
    pcaddlem.5
    simpld
    #
    zcnd
    #
    wph
    cS
    wph
    cS
    cn
    wcel
    #
    cP
    cS
    cdvds
    wbr
    wn
    #
    pcaddlem.6
    simpld
    #
    nncnd
    #
    wph
    @7
    cT
    @36
    @39
    mulcld
    @43
    wph
    cS
    @50
    nnne0d
    #
    @44
    divadddivd
    eqtr3d
    #
    oveq2d
    adantr
    @4
    @29
    @21
    cz
    wcel
    #
    @21
    cc0
    wne
    #
    @23
    cn
    wcel
    #
    @25
    @27
    wceq
    wph
    @29
    @3
    pcaddlem.1
    adantr
    #
    wph
    @54
    @3
    wph
    @18
    @20
    wph
    cR
    cU
    @46
    wph
    cU
    @42
    nnzd
    #
    zmulcld
    wph
    @19
    cS
    wph
    @7
    cT
    wph
    @7
    wph
    cP
    @6
    @31
    wph
    @14
    @6
    cn0
    wcel
    pcaddlem.4
    cM
    cN
    uznn0sub
    syl
    nnexpcld
    nnzd
    @38
    zmulcld
    wph
    cS
    @50
    nnzd
    #
    zmulcld
    zaddcld
    adantr
    #
    wph
    @3
    @55
    wph
    @3
    @24
    cc0
    wne
    #
    @55
    wph
    cP
    cM
    cexp
    co
    #
    @10
    cmul
    co
    #
    cc0
    wne
    #
    @10
    cc0
    wne
    #
    @3
    @61
    wph
    @10
    cc0
    @63
    cc0
    wph
    @63
    cc0
    wceq
    @10
    cc0
    wceq
    #
    @62
    cc0
    cmul
    co
    #
    cc0
    wceq
    wph
    @62
    wph
    cP
    cM
    @32
    @33
    @16
    expclzd
    #
    mul01d
    @66
    @63
    @67
    cc0
    @10
    cc0
    @62
    cmul
    oveq2
    eqeq1d
    syl5ibrcom
    necon3d
    #
    wph
    @63
    @0
    cc0
    wph
    @63
    @62
    @5
    cmul
    co
    #
    @62
    @9
    cmul
    co
    #
    caddc
    co
    @0
    wph
    @62
    @5
    @9
    @68
    wph
    cR
    cS
    @47
    @51
    @52
    divcld
    wph
    @7
    @8
    @36
    wph
    cT
    cU
    @39
    @43
    @44
    divcld
    #
    mulcld
    adddid
    wph
    cA
    @70
    cB
    @71
    caddc
    pcaddlem.2
    wph
    cB
    cP
    cN
    cexp
    co
    #
    @8
    cmul
    co
    @62
    @7
    cmul
    co
    #
    @8
    cmul
    co
    @71
    pcaddlem.3
    wph
    @73
    @74
    @8
    cmul
    wph
    cP
    cM
    @6
    caddc
    co
    #
    cexp
    co
    #
    @73
    @74
    wph
    @75
    cN
    cP
    cexp
    wph
    cM
    cN
    wph
    cM
    @16
    zcnd
    wph
    cN
    @34
    zcnd
    pncan3d
    oveq2d
    wph
    cP
    cc
    wcel
    cP
    cc0
    wne
    #
    @15
    @6
    cz
    wcel
    #
    @76
    @74
    wceq
    @32
    @33
    @16
    @35
    cP
    cM
    @6
    expaddz
    syl22anc
    eqtr3d
    oveq1d
    wph
    @62
    @7
    @8
    @68
    @36
    @72
    mulassd
    3eqtrd
    oveq12d
    eqtr4d
    #
    neeq1d
    #
    wph
    @10
    @24
    cc0
    @53
    neeq1d
    3imtr3d
    wph
    @21
    cc0
    @24
    cc0
    wph
    @24
    cc0
    wceq
    @21
    cc0
    wceq
    #
    cc0
    @23
    cdiv
    co
    #
    cc0
    wceq
    wph
    @23
    wph
    @23
    wph
    cS
    cU
    @50
    @42
    nnmulcld
    #
    nncnd
    wph
    @23
    @83
    nnne0d
    div0d
    @81
    @24
    @82
    cc0
    @21
    cc0
    @23
    cdiv
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    syld
    imp
    #
    wph
    @56
    @3
    @83
    adantr
    @21
    @23
    cP
    pcdiv
    syl121anc
    @4
    @27
    @22
    cc0
    cmin
    co
    #
    @22
    wph
    @27
    @85
    wceq
    @3
    wph
    @26
    cc0
    @22
    cmin
    wph
    @26
    cP
    cS
    cpc
    co
    #
    cP
    cU
    cpc
    co
    #
    caddc
    co
    #
    cc0
    wph
    @29
    cS
    cz
    wcel
    cS
    cc0
    wne
    cU
    cz
    wcel
    cU
    cc0
    wne
    @26
    @88
    wceq
    pcaddlem.1
    @59
    @52
    @58
    @44
    cS
    cU
    cP
    pcmul
    syl122anc
    wph
    @88
    cc0
    cc0
    caddc
    co
    cc0
    wph
    @86
    cc0
    @87
    cc0
    caddc
    wph
    @86
    cc0
    wceq
    #
    @49
    wph
    @48
    @49
    pcaddlem.6
    simprd
    wph
    @29
    @48
    @89
    @49
    wb
    pcaddlem.1
    @50
    cP
    cS
    pceq0
    syl2anc
    mpbird
    wph
    @87
    cc0
    wceq
    #
    @41
    wph
    @40
    @41
    pcaddlem.8
    simprd
    wph
    @29
    @40
    @90
    @41
    wb
    pcaddlem.1
    @42
    cP
    cU
    pceq0
    syl2anc
    mpbird
    oveq12d
    00id
    syl6eq
    eqtrd
    oveq2d
    adantr
    @4
    @22
    @4
    @22
    @4
    @29
    @54
    @55
    @22
    cn0
    wcel
    @57
    @60
    @84
    cP
    @21
    pczcl
    syl12anc
    #
    nn0cnd
    subid1d
    eqtrd
    3eqtrd
    @91
    eqeltrd
    cM
    @11
    nn0addge1
    syl2anc
    @4
    cP
    @63
    cpc
    co
    #
    cP
    @62
    cpc
    co
    #
    @11
    caddc
    co
    #
    @1
    @12
    @4
    @29
    @62
    cq
    wcel
    #
    @62
    cc0
    wne
    #
    @10
    cq
    wcel
    #
    @65
    @92
    @94
    wceq
    @57
    wph
    @95
    @3
    wph
    cP
    cq
    wcel
    #
    @77
    @15
    @95
    wph
    @30
    @98
    @31
    cP
    nnq
    syl
    #
    @33
    @16
    cP
    cM
    qexpclz
    syl3anc
    adantr
    wph
    @96
    @3
    wph
    cP
    cM
    @32
    @33
    @16
    expne0d
    adantr
    wph
    @97
    @3
    wph
    @5
    cq
    wcel
    #
    @9
    cq
    wcel
    #
    @97
    wph
    @45
    @48
    @100
    @46
    @50
    cR
    cS
    znq
    syl2anc
    wph
    @7
    cq
    wcel
    #
    @8
    cq
    wcel
    #
    @101
    wph
    @98
    @77
    @78
    @102
    @99
    @33
    @35
    cP
    @6
    qexpclz
    syl3anc
    wph
    @37
    @40
    @103
    @38
    @42
    cT
    cU
    znq
    syl2anc
    @7
    @8
    qmulcl
    syl2anc
    @5
    @9
    qaddcl
    syl2anc
    adantr
    wph
    @3
    @65
    wph
    @3
    @64
    @65
    @80
    @69
    sylbird
    imp
    @62
    @10
    cP
    pcqmul
    syl122anc
    wph
    @92
    @1
    wceq
    @3
    wph
    @63
    @0
    cP
    cpc
    @79
    oveq2d
    adantr
    wph
    @94
    @12
    wceq
    @3
    wph
    @93
    cM
    @11
    caddc
    wph
    @29
    @15
    @93
    cM
    wceq
    pcaddlem.1
    @16
    cM
    cP
    pcid
    syl2anc
    oveq1d
    adantr
    3eqtr3d
    breqtrrd
    wph
    cM
    cpnf
    @2
    cle
    wph
    cM
    cxr
    wcel
    cM
    cpnf
    cle
    wbr
    wph
    cM
    @17
    rexrd
    cM
    pnfge
    syl
    wph
    @29
    @2
    cpnf
    wceq
    pcaddlem.1
    cP
    pc0
    syl
    breqtrrd
    pm2.61ne
end
