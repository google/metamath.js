include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cee.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "cneg.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "cun.mm"
include "caddc.mm"
include "cif.mm"
include "wa.mm"
include "eqid.mm"
include "axlowdimlem7.mm"
include "adantr.mm"
include "cn.mm"
include "eluzge3nn.mm"
include "axlowdimlem10.mm"
include "sylan.mm"
include "ifcld.mm"
include "fmptd.mm"
include "wb.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "opeq1d.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "xpeq1d.mm"
include "uneq12d.mm"
include "ifbieq2d.mm"
include "snex.mm"
include "cvv.mm"
include "ovex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "xpex.mm"
include "unex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "eqtr3.mm"
include "2a1d.mm"
include "wn.mm"
include "axlowdimlem13.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "adantrl.mm"
include "iftrue.mm"
include "iffalse.mm"
include "imbi1d.mm"
include "syl5ibr.mm"
include "necomd.mm"
include "adantrr.mm"
include "axlowdimlem14.mm"
include "3expb.mm"
include "4cases.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem axlowdimlem15
  let vi: setvar i
  let cF: class F
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  assume axlowdimlem15.1: |- F = ( i e. ( 1 ... ( N - 1 ) ) |-> if ( i = 1 , ( { <. 3 , -u 1 >. } u. ( ( ( 1 ... N ) \ { 3 } ) X. { 0 } ) ) , ( { <. ( i + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( i + 1 ) } ) X. { 0 } ) ) ) )

  disjoint N i
  disjoint F j
  disjoint F k
  disjoint j k
  disjoint N j
  disjoint N k
  disjoint i j
  disjoint i k
  assert |- ( N e. ( ZZ>= ` 3 ) -> F : ( 1 ... ( N - 1 ) ) -1-1-> ( EE ` N ) )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    cN
    cee
    cfv
    #
    cF
    wf
    vj
    cv
    #
    cF
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vj
    vk
    weq
    #
    wi
    #
    vk
    @1
    wral
    vj
    @1
    wral
    @1
    @2
    cF
    wf1
    @0
    vi
    @1
    vi
    cv
    #
    c1
    wceq
    #
    c3
    c1
    cneg
    cop
    #
    csn
    #
    c1
    cN
    cfz
    co
    #
    c3
    csn
    #
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    @10
    c1
    caddc
    co
    #
    c1
    cop
    #
    csn
    #
    @14
    @20
    csn
    #
    cdif
    #
    @17
    cxp
    #
    cun
    #
    cif
    #
    @2
    cF
    @0
    @10
    @1
    wcel
    #
    wa
    @11
    @19
    @26
    @2
    @0
    @19
    @2
    wcel
    @28
    @19
    cN
    @19
    eqid
    #
    axlowdimlem7
    adantr
    @0
    cN
    cn
    wcel
    #
    @28
    @26
    @2
    wcel
    cN
    eluzge3nn
    #
    @26
    @10
    cN
    @26
    eqid
    axlowdimlem10
    sylan
    ifcld
    axlowdimlem15.1
    fmptd
    @0
    @9
    vj
    vk
    @1
    @1
    @0
    @3
    @1
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    #
    wa
    #
    @7
    @3
    c1
    wceq
    #
    @19
    @3
    c1
    caddc
    co
    #
    c1
    cop
    #
    csn
    #
    @14
    @37
    csn
    #
    cdif
    #
    @17
    cxp
    #
    cun
    #
    cif
    #
    @5
    c1
    wceq
    #
    @19
    @5
    c1
    caddc
    co
    #
    c1
    cop
    #
    csn
    #
    @14
    @46
    csn
    #
    cdif
    #
    @17
    cxp
    #
    cun
    #
    cif
    #
    wceq
    #
    @8
    @34
    @7
    @54
    wb
    @0
    @32
    @33
    @4
    @44
    @6
    @53
    vi
    @3
    @27
    @44
    @1
    cF
    vi
    vj
    weq
    #
    @11
    @36
    @26
    @43
    @19
    @10
    @3
    c1
    eqeq1
    @55
    @22
    @39
    @25
    @42
    @55
    @21
    @38
    @55
    @20
    @37
    c1
    @10
    @3
    c1
    caddc
    oveq1
    #
    opeq1d
    sneqd
    @55
    @24
    @41
    @17
    @55
    @23
    @40
    @14
    @55
    @20
    @37
    @56
    sneqd
    difeq2d
    xpeq1d
    uneq12d
    ifbieq2d
    axlowdimlem15.1
    @36
    @19
    @43
    @13
    @18
    @12
    snex
    @16
    @17
    @14
    cvv
    wcel
    #
    @16
    cvv
    wcel
    c1
    cN
    cfz
    ovex
    #
    @14
    @15
    cvv
    difexg
    ax-mp
    cc0
    snex
    #
    xpex
    unex
    #
    @39
    @42
    @38
    snex
    @41
    @17
    @57
    @41
    cvv
    wcel
    @58
    @14
    @40
    cvv
    difexg
    ax-mp
    @59
    xpex
    unex
    ifex
    fvmpt
    vi
    @5
    @27
    @53
    @1
    cF
    vi
    vk
    weq
    #
    @11
    @45
    @26
    @52
    @19
    @10
    @5
    c1
    eqeq1
    @61
    @22
    @48
    @25
    @51
    @61
    @21
    @47
    @61
    @20
    @46
    c1
    @10
    @5
    c1
    caddc
    oveq1
    #
    opeq1d
    sneqd
    @61
    @24
    @50
    @17
    @61
    @23
    @49
    @14
    @61
    @20
    @46
    @62
    sneqd
    difeq2d
    xpeq1d
    uneq12d
    ifbieq2d
    axlowdimlem15.1
    @45
    @19
    @52
    @60
    @48
    @51
    @47
    snex
    @50
    @17
    @57
    @50
    cvv
    wcel
    @58
    @14
    @49
    cvv
    difexg
    ax-mp
    @59
    xpex
    unex
    ifex
    fvmpt
    eqeqan12d
    adantl
    @36
    @45
    @35
    @54
    @8
    wi
    #
    wi
    @36
    @45
    wa
    @8
    @35
    @54
    @3
    @5
    c1
    eqtr3
    2a1d
    @35
    @63
    @36
    @45
    wn
    #
    wa
    #
    @19
    @52
    wceq
    #
    @8
    wi
    #
    @0
    @30
    @34
    @67
    @31
    @30
    @33
    @67
    @32
    @30
    @33
    wa
    #
    @66
    @8
    @68
    @19
    @52
    @19
    @52
    @5
    cN
    @29
    @52
    eqid
    #
    axlowdimlem13
    neneqd
    pm2.21d
    adantrl
    sylan
    @65
    @54
    @66
    @8
    @36
    @64
    @44
    @19
    @53
    @52
    @36
    @19
    @43
    iftrue
    @45
    @19
    @52
    iffalse
    #
    eqeqan12d
    imbi1d
    syl5ibr
    @35
    @63
    @36
    wn
    #
    @45
    wa
    #
    @43
    @19
    wceq
    #
    @8
    wi
    #
    @0
    @32
    @74
    @33
    @0
    @30
    @32
    @74
    @31
    @30
    @32
    wa
    #
    @73
    @8
    @75
    @43
    @19
    @75
    @19
    @43
    @19
    @43
    @3
    cN
    @29
    @43
    eqid
    #
    axlowdimlem13
    necomd
    neneqd
    pm2.21d
    sylan
    adantrr
    @72
    @54
    @73
    @8
    @71
    @45
    @44
    @43
    @53
    @19
    @36
    @19
    @43
    iffalse
    #
    @45
    @19
    @52
    iftrue
    eqeqan12d
    imbi1d
    syl5ibr
    @35
    @63
    @71
    @64
    wa
    #
    @43
    @52
    wceq
    #
    @8
    wi
    #
    @0
    @30
    @34
    @80
    @31
    @30
    @32
    @33
    @80
    @43
    @52
    @3
    @5
    cN
    @76
    @69
    axlowdimlem14
    3expb
    sylan
    @78
    @54
    @79
    @8
    @71
    @64
    @44
    @43
    @53
    @52
    @77
    @70
    eqeqan12d
    imbi1d
    syl5ibr
    4cases
    sylbid
    ralrimivva
    vj
    vk
    @1
    @2
    cF
    dff13
    sylanbrc
end
