include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "ci.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cexp.mm"
include "cmin.mm"
include "clog.mm"
include "ce.mm"
include "cpi.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "neg1cn.mm"
include "neg1ne0.mm"
include "cr.mm"
include "cn.mm"
include "2re.mm"
include "3nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "recni.mm"
include "cxpef.mm"
include "mp3an.mm"
include "logm1.mm"
include "oveq2i.mm"
include "ax-icn.mm"
include "pire.mm"
include "mul12i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "ccos.mm"
include "csin.mm"
include "c6.mm"
include "6nn.mm"
include "coshalfpip.mm"
include "ax-mp.mm"
include "2cn.mm"
include "2ne0.mm"
include "divrec2.mm"
include "6cn.mm"
include "nnne0i.mm"
include "oveq12i.mm"
include "reccli.mm"
include "adddiri.mm"
include "halfpm6th.mm"
include "simpri.mm"
include "oveq1i.mm"
include "3eqtr2i.mm"
include "sincos6thpi.mm"
include "simpli.mm"
include "negeqi.mm"
include "ax-1cn.mm"
include "divneg.mm"
include "3eqtr3i.mm"
include "sinhalfpip.mm"
include "cle.mm"
include "wbr.mm"
include "3re.mm"
include "3nn0.mm"
include "nn0ge0i.mm"
include "resqrtcl.mm"
include "divassi.mm"
include "eqtr4i.mm"
include "mulcli.mm"
include "efival.mm"
include "divdiri.mm"
include "3eqtr4i.mm"
include "3eqtri.mm"
include "ccj.mm"
include "cz.mm"
include "1z.mm"
include "root1cj.mm"
include "cxpcl.mm"
include "exp1.mm"
include "addcli.mm"
include "cjdivi.mm"
include "cjaddi.mm"
include "neg1rr.mm"
include "cjre.mm"
include "cjmuli.mm"
include "cji.mm"
include "mulneg1i.mm"
include "negsubi.mm"
include "3m1e2.mm"
include "3eqtr3ri.mm"
include "pm3.2i.mm"

theorem 1cubrlem



  assert |- ( ( -u 1 ^c ( 2 / 3 ) ) = ( ( -u 1 + ( _i x. ( sqrt ` 3 ) ) ) / 2 ) /\ ( ( -u 1 ^c ( 2 / 3 ) ) ^ 2 ) = ( ( -u 1 - ( _i x. ( sqrt ` 3 ) ) ) / 2 ) )

  proof
    c1
    cneg
    #
    c2
    c3
    cdiv
    co
    #
    ccxp
    co
    #
    @0
    ci
    c3
    csqrt
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    wceq
    @2
    c2
    cexp
    co
    #
    @0
    @4
    cmin
    co
    #
    c2
    cdiv
    co
    #
    wceq
    @2
    @1
    @0
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    @1
    cpi
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    @1
    cc
    wcel
    #
    @2
    @12
    wceq
    neg1cn
    neg1ne0
    @1
    c2
    cr
    wcel
    #
    c3
    cn
    wcel
    #
    @1
    cr
    wcel
    2re
    3nn
    c2
    c3
    nndivre
    mp2an
    recni
    #
    @0
    @1
    cxpef
    mp3an
    @11
    @14
    ce
    @11
    @1
    ci
    cpi
    cmul
    co
    #
    cmul
    co
    @14
    @10
    @21
    @1
    cmul
    logm1
    oveq2i
    @1
    ci
    cpi
    @20
    ax-icn
    cpi
    pire
    recni
    #
    mul12i
    eqtri
    fveq2i
    @13
    ccos
    cfv
    #
    ci
    @13
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @0
    c2
    cdiv
    co
    #
    @4
    c2
    cdiv
    co
    #
    caddc
    co
    @15
    @6
    @23
    @27
    @25
    @28
    caddc
    cpi
    c2
    cdiv
    co
    #
    cpi
    c6
    cdiv
    co
    #
    caddc
    co
    #
    ccos
    cfv
    #
    @30
    csin
    cfv
    #
    cneg
    #
    @23
    @27
    @30
    cc
    wcel
    #
    @32
    @34
    wceq
    @30
    cpi
    cr
    wcel
    c6
    cn
    wcel
    @30
    cr
    wcel
    pire
    6nn
    cpi
    c6
    nndivre
    mp2an
    recni
    #
    @30
    coshalfpip
    ax-mp
    @31
    @13
    ccos
    @31
    c1
    c2
    cdiv
    co
    #
    cpi
    cmul
    co
    #
    c1
    c6
    cdiv
    co
    #
    cpi
    cmul
    co
    #
    caddc
    co
    @37
    @39
    caddc
    co
    #
    cpi
    cmul
    co
    @13
    @29
    @38
    @30
    @40
    caddc
    cpi
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @29
    @38
    wceq
    @22
    2cn
    2ne0
    cpi
    c2
    divrec2
    mp3an
    @42
    c6
    cc
    wcel
    c6
    cc0
    wne
    @30
    @40
    wceq
    @22
    6cn
    c6
    6nn
    nnne0i
    #
    cpi
    c6
    divrec2
    mp3an
    oveq12i
    @37
    @39
    cpi
    c2
    2cn
    2ne0
    reccli
    c6
    6cn
    @45
    reccli
    @22
    adddiri
    @41
    @1
    cpi
    cmul
    @37
    @39
    cmin
    co
    c1
    c3
    cdiv
    co
    wceq
    @41
    @1
    wceq
    halfpm6th
    simpri
    oveq1i
    3eqtr2i
    #
    fveq2i
    @34
    @37
    cneg
    #
    @27
    @33
    @37
    @33
    @37
    wceq
    #
    @30
    ccos
    cfv
    #
    @3
    c2
    cdiv
    co
    #
    wceq
    #
    sincos6thpi
    simpli
    negeqi
    c1
    cc
    wcel
    @43
    @44
    @47
    @27
    wceq
    ax-1cn
    2cn
    2ne0
    c1
    c2
    divneg
    mp3an
    eqtri
    3eqtr3i
    @25
    ci
    @50
    cmul
    co
    @28
    @24
    @50
    ci
    cmul
    @31
    csin
    cfv
    #
    @49
    @24
    @50
    @35
    @52
    @49
    wceq
    @36
    @30
    sinhalfpip
    ax-mp
    @31
    @13
    csin
    @46
    fveq2i
    @48
    @51
    sincos6thpi
    simpri
    3eqtr3i
    oveq2i
    ci
    @3
    c2
    ax-icn
    @3
    c3
    cr
    wcel
    cc0
    c3
    cle
    wbr
    @3
    cr
    wcel
    #
    3re
    c3
    3nn0
    nn0ge0i
    c3
    resqrtcl
    mp2an
    #
    recni
    #
    2cn
    2ne0
    divassi
    eqtr4i
    oveq12i
    @13
    cc
    wcel
    @15
    @26
    wceq
    @1
    cpi
    @20
    @22
    mulcli
    @13
    efival
    ax-mp
    @0
    @4
    c2
    neg1cn
    ci
    @3
    ax-icn
    @55
    mulcli
    #
    2cn
    2ne0
    divdiri
    3eqtr4i
    3eqtri
    #
    @2
    c1
    cexp
    co
    #
    ccj
    cfv
    #
    @2
    c3
    c1
    cmin
    co
    #
    cexp
    co
    #
    @9
    @7
    @19
    c1
    cz
    wcel
    @59
    @61
    wceq
    3nn
    1z
    c1
    c3
    root1cj
    mp2an
    @59
    @6
    ccj
    cfv
    #
    @5
    ccj
    cfv
    #
    c2
    ccj
    cfv
    #
    cdiv
    co
    #
    @9
    @58
    @6
    ccj
    @58
    @2
    @6
    @2
    cc
    wcel
    #
    @58
    @2
    wceq
    @16
    @17
    @66
    neg1cn
    @20
    @0
    @1
    cxpcl
    mp2an
    @2
    exp1
    ax-mp
    @57
    eqtri
    fveq2i
    @44
    @62
    @65
    wceq
    2ne0
    @5
    c2
    @0
    @4
    neg1cn
    @56
    addcli
    2cn
    cjdivi
    ax-mp
    @63
    @8
    @64
    c2
    cdiv
    @63
    @0
    ccj
    cfv
    #
    @4
    ccj
    cfv
    #
    caddc
    co
    @0
    @4
    cneg
    #
    caddc
    co
    @8
    @0
    @4
    neg1cn
    @56
    cjaddi
    @67
    @0
    @68
    @69
    caddc
    @0
    cr
    wcel
    @67
    @0
    wceq
    neg1rr
    @0
    cjre
    ax-mp
    @68
    ci
    ccj
    cfv
    #
    @3
    ccj
    cfv
    #
    cmul
    co
    ci
    cneg
    #
    @3
    cmul
    co
    @69
    ci
    @3
    ax-icn
    @55
    cjmuli
    @70
    @72
    @71
    @3
    cmul
    cji
    @53
    @71
    @3
    wceq
    @54
    @3
    cjre
    ax-mp
    oveq12i
    ci
    @3
    ax-icn
    @55
    mulneg1i
    3eqtri
    oveq12i
    @0
    @4
    neg1cn
    @56
    negsubi
    3eqtri
    @18
    @64
    c2
    wceq
    2re
    c2
    cjre
    ax-mp
    oveq12i
    3eqtri
    @60
    c2
    @2
    cexp
    3m1e2
    oveq2i
    3eqtr3ri
    pm3.2i
end
