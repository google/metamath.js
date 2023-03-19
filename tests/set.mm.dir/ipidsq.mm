include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cmin.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "wceq.mm"
include "eqid.mm"
include "ipval2.mm"
include "3anidm23.mm"
include "cc0.mm"
include "nv2.mm"
include "fveq2d.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "2re.mm"
include "0le2.mm"
include "pm3.2i.mm"
include "nvsge0.mm"
include "mp3an2.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cc.mm"
include "nvcl.mm"
include "recnd.mm"
include "cn0.mm"
include "2cn.mm"
include "2nn0.mm"
include "mulexp.mm"
include "mp3an13.mm"
include "syl.mm"
include "sq2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "cn0v.mm"
include "nvrinv.mm"
include "nvz0.mm"
include "adantr.mm"
include "sq0id.mm"
include "oveq12d.mm"
include "4cn.mm"
include "sqcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subid1d.mm"
include "cabs.mm"
include "csqrt.mm"
include "1re.mm"
include "neg1rr.mm"
include "absreim.mm"
include "mp2an.mm"
include "ax-icn.mm"
include "ax-1cn.mm"
include "mulneg2i.mm"
include "mulid1i.mm"
include "negeqi.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "sqneg.mm"
include "ax-mp.mm"
include "3eqtr3i.mm"
include "3eqtr2i.mm"
include "negicn.mm"
include "addcli.mm"
include "nvs.mm"
include "3eqtr4a.mm"
include "nvdir.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "nvsid.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "w3a.mm"
include "ipval2lem4.mm"
include "mpan2.mm"
include "subidd.mm"
include "it0e0.mm"
include "addid1d.mm"
include "eqtr2d.mm"
include "wne.mm"
include "4ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "3eqtr2d.mm"

theorem ipidsq
  let cA: class A
  let cP: class P
  let cU: class U
  let cN: class N
  let cX: class X
  assume ipid.1: |- X = ( BaseSet ` U )
  assume ipid.6: |- N = ( normCV ` U )
  assume ipid.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A P A ) = ( ( N ` A ) ^ 2 ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cA
    cP
    co
    #
    cA
    cA
    cU
    cpv
    cfv
    #
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cA
    cU
    cns
    cfv
    #
    co
    @4
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cA
    @9
    co
    #
    @4
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
    cA
    @9
    co
    #
    @4
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    c4
    cA
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    c4
    cdiv
    co
    #
    @28
    @0
    @1
    @3
    @26
    wceq
    cA
    cA
    cP
    @9
    cU
    @4
    cN
    cX
    ipid.1
    @4
    eqid
    #
    @9
    eqid
    #
    ipid.6
    ipid.7
    ipval2
    3anidm23
    @2
    @29
    @25
    c4
    cdiv
    @2
    @25
    @29
    cc0
    caddc
    co
    @29
    @2
    @13
    @29
    @24
    cc0
    caddc
    @2
    @13
    @29
    cc0
    cmin
    co
    @29
    @2
    @7
    @29
    @12
    cc0
    cmin
    @2
    @7
    c2
    @27
    cmul
    co
    #
    c2
    cexp
    co
    #
    @29
    @2
    @6
    @33
    c2
    cexp
    @2
    @6
    c2
    cA
    @9
    co
    #
    cN
    cfv
    #
    @33
    @2
    @5
    @35
    cN
    cA
    @9
    cU
    @4
    cX
    ipid.1
    @31
    @32
    nv2
    fveq2d
    @0
    c2
    cr
    wcel
    #
    cc0
    c2
    cle
    wbr
    #
    wa
    @1
    @36
    @33
    wceq
    @37
    @38
    2re
    0le2
    pm3.2i
    c2
    cA
    @9
    cU
    cN
    cX
    ipid.1
    @32
    ipid.6
    nvsge0
    mp3an2
    eqtrd
    oveq1d
    @2
    @34
    c2
    c2
    cexp
    co
    #
    @28
    cmul
    co
    #
    @29
    @2
    @27
    cc
    wcel
    #
    @34
    @40
    wceq
    #
    @2
    @27
    cA
    cU
    cN
    cX
    ipid.1
    ipid.6
    nvcl
    recnd
    #
    c2
    cc
    wcel
    @41
    c2
    cn0
    wcel
    @42
    2cn
    2nn0
    c2
    @27
    c2
    mulexp
    mp3an13
    syl
    @39
    c4
    @28
    cmul
    sq2
    oveq1i
    syl6eq
    eqtrd
    @2
    @11
    @2
    @11
    cU
    cn0v
    cfv
    #
    cN
    cfv
    #
    cc0
    @2
    @10
    @44
    cN
    cA
    @9
    cU
    @4
    cX
    @44
    ipid.1
    @31
    @32
    @44
    eqid
    #
    nvrinv
    fveq2d
    @0
    @45
    cc0
    wceq
    @1
    cU
    cN
    @44
    @46
    ipid.6
    nvz0
    adantr
    eqtrd
    sq0id
    oveq12d
    @2
    @29
    @2
    c4
    cc
    wcel
    #
    @28
    cc
    wcel
    #
    @29
    cc
    wcel
    4cn
    @2
    @27
    @43
    sqcld
    #
    c4
    @28
    mulcl
    sylancr
    #
    subid1d
    eqtrd
    @2
    @24
    ci
    cc0
    cmul
    co
    cc0
    @2
    @23
    cc0
    ci
    cmul
    @2
    @23
    @17
    @17
    cmin
    co
    cc0
    @2
    @22
    @17
    @17
    cmin
    @2
    @21
    @16
    c2
    cexp
    @2
    c1
    @18
    caddc
    co
    #
    cA
    @9
    co
    #
    cN
    cfv
    #
    c1
    ci
    caddc
    co
    #
    cA
    @9
    co
    #
    cN
    cfv
    #
    @21
    @16
    @2
    @51
    cabs
    cfv
    #
    @27
    cmul
    co
    #
    @54
    cabs
    cfv
    #
    @27
    cmul
    co
    #
    @53
    @56
    @57
    @59
    @27
    cmul
    @57
    c1
    c2
    cexp
    co
    #
    @61
    caddc
    co
    #
    csqrt
    cfv
    #
    c1
    ci
    c1
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    @59
    c1
    ci
    @8
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    @61
    @8
    c2
    cexp
    co
    #
    caddc
    co
    #
    csqrt
    cfv
    #
    @57
    @63
    c1
    cr
    wcel
    #
    @8
    cr
    wcel
    @69
    @72
    wceq
    1re
    neg1rr
    c1
    @8
    absreim
    mp2an
    @68
    @51
    cabs
    @67
    @18
    c1
    caddc
    @67
    @64
    cneg
    @18
    ci
    c1
    ax-icn
    ax-1cn
    mulneg2i
    @64
    ci
    ci
    ax-icn
    mulid1i
    #
    negeqi
    eqtri
    oveq2i
    fveq2i
    @71
    @62
    csqrt
    @70
    @61
    @61
    caddc
    c1
    cc
    wcel
    #
    @70
    @61
    wceq
    ax-1cn
    c1
    sqneg
    ax-mp
    oveq2i
    fveq2i
    3eqtr3i
    @73
    @73
    @66
    @63
    wceq
    1re
    1re
    c1
    c1
    absreim
    mp2an
    @65
    @54
    cabs
    @64
    ci
    c1
    caddc
    @74
    oveq2i
    fveq2i
    3eqtr2i
    oveq1i
    @0
    @51
    cc
    wcel
    @1
    @53
    @58
    wceq
    c1
    @18
    ax-1cn
    negicn
    addcli
    @51
    cA
    @9
    cU
    cN
    cX
    ipid.1
    @32
    ipid.6
    nvs
    mp3an2
    @0
    @54
    cc
    wcel
    @1
    @56
    @60
    wceq
    c1
    ci
    ax-1cn
    ax-icn
    addcli
    @54
    cA
    @9
    cU
    cN
    cX
    ipid.1
    @32
    ipid.6
    nvs
    mp3an2
    3eqtr4a
    @2
    @52
    @20
    cN
    @2
    @52
    c1
    cA
    @9
    co
    #
    @19
    @4
    co
    #
    @20
    @0
    @18
    cc
    wcel
    #
    @1
    @52
    @77
    wceq
    #
    negicn
    @0
    @75
    @78
    @1
    @79
    ax-1cn
    c1
    @18
    cA
    @9
    cU
    @4
    cX
    ipid.1
    @31
    @32
    nvdir
    mp3anr1
    mpanr1
    @2
    @76
    cA
    @19
    @4
    cA
    @9
    cU
    cX
    ipid.1
    @32
    nvsid
    #
    oveq1d
    eqtrd
    fveq2d
    @2
    @55
    @15
    cN
    @2
    @55
    @76
    @14
    @4
    co
    #
    @15
    @0
    ci
    cc
    wcel
    #
    @1
    @55
    @81
    wceq
    #
    ax-icn
    @0
    @75
    @82
    @1
    @83
    ax-1cn
    c1
    ci
    cA
    @9
    cU
    @4
    cX
    ipid.1
    @31
    @32
    nvdir
    mp3anr1
    mpanr1
    @2
    @76
    cA
    @14
    @4
    @80
    oveq1d
    eqtrd
    fveq2d
    3eqtr3d
    oveq1d
    oveq2d
    @2
    @17
    @0
    @1
    @17
    cc
    wcel
    #
    @0
    @1
    @1
    w3a
    @82
    @84
    ax-icn
    cA
    cA
    ci
    cP
    @9
    cU
    @4
    cN
    cX
    ipid.1
    @31
    @32
    ipid.6
    ipid.7
    ipval2lem4
    mpan2
    3anidm23
    subidd
    eqtrd
    oveq2d
    it0e0
    syl6eq
    oveq12d
    @2
    @29
    @50
    addid1d
    eqtr2d
    oveq1d
    @2
    @48
    @30
    @28
    wceq
    #
    @49
    @48
    @47
    c4
    cc0
    wne
    @85
    4cn
    4ne0
    @28
    c4
    divcan3
    mp3an23
    syl
    3eqtr2d
end
