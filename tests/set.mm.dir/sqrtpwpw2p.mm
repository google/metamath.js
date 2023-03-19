include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "csqrt.mm"
include "cfv.mm"
include "cfl.mm"
include "wceq.mm"
include "cle.mm"
include "wa.mm"
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "adantr.mm"
include "npcan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "2cnd.mm"
include "nnm1nn0.mm"
include "expp1d.mm"
include "eqtrd.mm"
include "2nn0.mm"
include "a1i.mm"
include "nn0expcld.mm"
include "expmuld.mm"
include "cc0.mm"
include "nn0ge0.mm"
include "adantl.mm"
include "cr.mm"
include "wb.mm"
include "nnnn0.mm"
include "nn0red.mm"
include "nn0re.mm"
include "anim12i.mm"
include "addge01.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "simpr.mm"
include "nn0addcld.mm"
include "jca.mm"
include "resqrtth.mm"
include "breqtrrd.mm"
include "resqrtcl.mm"
include "sqrtge0.mm"
include "le2sq.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "3adant3.mm"
include "wi.mm"
include "peano2nn0.mm"
include "axltadd.mm"
include "syl3anc.mm"
include "3impia.mm"
include "nn0cnd.mm"
include "3ad2ant1.mm"
include "1cnd.mm"
include "addassd.mm"
include "binom21.mm"
include "eqtr3d.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "addge0.mm"
include "resqrtcld.mm"
include "lt2sq.mm"
include "syl21anc.mm"
include "cz.mm"
include "nn0zd.mm"
include "flbi.mm"

theorem sqrtpwpw2p
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN /\ M e. NN0 /\ M < ( ( 2 ^ ( ( 2 ^ ( N - 1 ) ) + 1 ) ) + 1 ) ) -> ( |_ ` ( sqrt ` ( ( 2 ^ ( 2 ^ N ) ) + M ) ) ) = ( 2 ^ ( 2 ^ ( N - 1 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    c2
    c2
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    clt
    wbr
    #
    w3a
    #
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    cM
    caddc
    co
    #
    csqrt
    cfv
    #
    cfl
    cfv
    c2
    @3
    cexp
    co
    #
    wceq
    #
    @13
    @12
    cle
    wbr
    #
    @12
    @13
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    @8
    @15
    @17
    @0
    @1
    @15
    @7
    @0
    @1
    wa
    #
    @15
    @13
    c2
    cexp
    co
    #
    @12
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @19
    @20
    @11
    @21
    cle
    @19
    @10
    @20
    @11
    cle
    @19
    @10
    c2
    @3
    c2
    cmul
    co
    #
    cexp
    co
    #
    @20
    @19
    @9
    @23
    c2
    cexp
    @19
    @9
    c2
    @2
    c1
    caddc
    co
    #
    cexp
    co
    #
    @23
    @19
    cN
    @25
    c2
    cexp
    @19
    @25
    cN
    @19
    cN
    cc
    wcel
    #
    @25
    cN
    wceq
    #
    @0
    @27
    @1
    cN
    nncn
    #
    adantr
    cN
    npcan1
    #
    syl
    eqcomd
    oveq2d
    @19
    c2
    @2
    @19
    2cnd
    #
    @0
    @2
    cn0
    wcel
    @1
    cN
    nnm1nn0
    #
    adantr
    expp1d
    eqtrd
    oveq2d
    @19
    c2
    @3
    c2
    @31
    c2
    cn0
    wcel
    #
    @19
    2nn0
    a1i
    @0
    @3
    cn0
    wcel
    #
    @1
    @0
    c2
    @2
    @33
    @0
    2nn0
    a1i
    #
    @32
    nn0expcld
    #
    adantr
    expmuld
    eqtrd
    @19
    cc0
    cM
    cle
    wbr
    #
    @10
    @11
    cle
    wbr
    #
    @1
    @37
    @0
    cM
    nn0ge0
    #
    adantl
    @19
    @10
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    wa
    #
    @37
    @38
    wb
    @0
    @40
    @1
    @41
    @0
    @10
    @0
    c2
    @9
    @35
    @0
    c2
    cN
    @35
    cN
    nnnn0
    nn0expcld
    nn0expcld
    #
    nn0red
    cM
    nn0re
    #
    anim12i
    #
    @10
    cM
    addge01
    syl
    mpbid
    eqbrtrrd
    @19
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    wa
    #
    @21
    @11
    wceq
    @19
    @11
    cn0
    wcel
    #
    @48
    @19
    @10
    cM
    @0
    @10
    cn0
    wcel
    #
    @1
    @43
    adantr
    #
    @0
    @1
    simpr
    nn0addcld
    #
    @49
    @46
    @47
    @11
    nn0re
    @11
    nn0ge0
    jca
    syl
    #
    @11
    resqrtth
    syl
    #
    breqtrrd
    @19
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    wa
    #
    @12
    cr
    wcel
    #
    cc0
    @12
    cle
    wbr
    #
    @15
    @22
    wb
    @0
    @57
    @1
    @0
    @13
    cn0
    wcel
    #
    @57
    @0
    c2
    @3
    @35
    @36
    nn0expcld
    #
    @60
    @55
    @56
    @13
    nn0re
    @13
    nn0ge0
    jca
    syl
    adantr
    @19
    @48
    @58
    @53
    @11
    resqrtcl
    syl
    #
    @19
    @48
    @59
    @53
    @11
    sqrtge0
    syl
    #
    @13
    @12
    le2sq
    syl12anc
    mpbird
    3adant3
    @8
    @17
    @21
    @16
    c2
    cexp
    co
    #
    clt
    wbr
    #
    @8
    @65
    @11
    @10
    @5
    caddc
    co
    #
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @8
    @11
    @10
    @6
    caddc
    co
    #
    @67
    clt
    @0
    @1
    @7
    @11
    @69
    clt
    wbr
    #
    @19
    @41
    @6
    cr
    wcel
    @40
    @7
    @70
    wi
    @1
    @41
    @0
    @44
    adantl
    @19
    @6
    @19
    @5
    cn0
    wcel
    #
    @6
    cn0
    wcel
    @0
    @71
    @1
    @0
    c2
    @4
    @35
    @0
    @34
    @4
    cn0
    wcel
    @36
    @3
    peano2nn0
    syl
    nn0expcld
    #
    adantr
    @5
    peano2nn0
    syl
    nn0red
    @19
    @10
    @51
    nn0red
    cM
    @6
    @10
    axltadd
    syl3anc
    3impia
    @8
    @10
    @5
    c1
    @0
    @1
    @10
    cc
    wcel
    @7
    @0
    @10
    @43
    nn0cnd
    3ad2ant1
    @0
    @1
    @5
    cc
    wcel
    @7
    @0
    @5
    @72
    nn0cnd
    3ad2ant1
    @8
    1cnd
    addassd
    breqtrrd
    @0
    @1
    @65
    @68
    wb
    @7
    @19
    @21
    @11
    @64
    @67
    clt
    @54
    @0
    @64
    @67
    wceq
    @1
    @0
    @64
    @20
    c2
    @13
    cmul
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @67
    @0
    @13
    cc
    wcel
    @64
    @75
    wceq
    @0
    @13
    @61
    nn0cnd
    #
    @13
    binom21
    syl
    @0
    @74
    @66
    c1
    caddc
    @0
    @20
    @10
    @73
    @5
    caddc
    @0
    @24
    @20
    @10
    @0
    c2
    @3
    c2
    @0
    2cnd
    #
    @35
    @36
    expmuld
    @0
    @23
    @9
    c2
    cexp
    @0
    @26
    @23
    @9
    @0
    c2
    @2
    @77
    @32
    expp1d
    @0
    @25
    cN
    c2
    cexp
    @0
    @27
    @28
    @29
    @30
    syl
    oveq2d
    eqtr3d
    oveq2d
    eqtr3d
    @0
    @73
    @13
    c2
    cmul
    co
    @5
    @0
    c2
    @13
    @77
    @76
    mulcomd
    @0
    c2
    @3
    @77
    @36
    expp1d
    eqtr4d
    oveq12d
    oveq1d
    eqtrd
    adantr
    breq12d
    3adant3
    mpbird
    @0
    @1
    @17
    @65
    wb
    #
    @7
    @19
    @58
    @59
    @16
    cr
    wcel
    #
    cc0
    @16
    cle
    wbr
    #
    wa
    #
    @78
    @19
    @11
    @19
    @11
    @52
    nn0red
    @19
    @42
    cc0
    @10
    cle
    wbr
    #
    @37
    wa
    #
    wa
    @47
    @19
    @42
    @83
    @45
    @0
    @82
    @1
    @37
    @0
    @50
    @82
    @43
    @10
    nn0ge0
    syl
    @39
    anim12i
    jca
    @10
    cM
    addge0
    syl
    resqrtcld
    @63
    @0
    @81
    @1
    @0
    @16
    cn0
    wcel
    #
    @81
    @0
    @60
    @84
    @61
    @13
    peano2nn0
    syl
    @84
    @79
    @80
    @16
    nn0re
    @16
    nn0ge0
    jca
    syl
    adantr
    @12
    @16
    lt2sq
    syl21anc
    3adant3
    mpbird
    jca
    @8
    @58
    @13
    cz
    wcel
    #
    wa
    #
    @14
    @18
    wb
    @0
    @1
    @86
    @7
    @19
    @58
    @85
    @62
    @0
    @85
    @1
    @0
    @13
    @61
    nn0zd
    adantr
    jca
    3adant3
    @12
    @13
    flbi
    syl
    mpbird
end
