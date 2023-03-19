include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cpnf.mm"
include "wceq.mm"
include "ciun.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "cres.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cc0.mm"
include "cicc.mm"
include "wf.mm"
include "come.mm"
include "adantr.mm"
include "wss.mm"
include "ffvelrnda.mm"
include "elpw.mm"
include "sylib.mm"
include "omecl.mm"
include "eqid.mm"
include "fmptd.mm"
include "simpr.mm"
include "cr.mm"
include "sge0pnffigt.mm"
include "wi.mm"
include "simpl.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "adantll.mm"
include "cxr.mm"
include "rexrd.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "sge0xrcl.mm"
include "elinel2.mm"
include "adantl.mm"
include "cico.mm"
include "rge0ssre.mm"
include "0xr.mm"
include "pnfxr.mm"
include "omexrcl.mm"
include "cle.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "ssiun2.mm"
include "syl.mm"
include "omessle.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "elicod.mm"
include "sseldi.mm"
include "fsumrecl.mm"
include "rpred.mm"
include "readdcld.mm"
include "sge0fsum.mm"
include "eqidd.mm"
include "fveq2.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "sumeq2dv.mm"
include "cbvsumv.mm"
include "3eqtrd.mm"
include "crp.mm"
include "ltaddrpd.mm"
include "eqbrtrd.mm"
include "xrlttrd.mm"
include "syl2anc.mm"
include "ex.mm"
include "adantlr.mm"
include "reximdva.mm"
include "mpd.mm"
include "wn.mm"
include "wb.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfel.mm"
include "nfan.mm"
include "sge0ltfirpmpt.mm"
include "ad3antrrr.mm"
include "ad4ant13.mm"
include "omeiunle.mm"
include "simpll.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "adantllr.mm"
include "sge0fsummpt.mm"
include "syl21anc.mm"
include "oveq1d.mm"
include "lelttrd.mm"
include "pm2.61dan.mm"

theorem omeiunltfirp
  let wph: wff ph
  let vz: setvar z
  let vn: setvar n
  let cE: class E
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  assume omeiunltfirp.o: |- ( ph -> O e. OutMeas )
  assume omeiunltfirp.x: |- X = U. dom O
  assume omeiunltfirp.z: |- Z = ( ZZ>= ` N )
  assume omeiunltfirp.e: |- ( ph -> E : Z --> ~P X )
  assume omeiunltfirp.re: |- ( ph -> ( O ` U_ n e. Z ( E ` n ) ) e. RR )
  assume omeiunltfirp.y: |- ( ph -> Y e. RR+ )

  disjoint E n
  disjoint E z
  disjoint n z
  disjoint O n
  disjoint O z
  disjoint X n
  disjoint Y z
  disjoint Z n
  disjoint Z z
  disjoint n ph
  disjoint ph z
  disjoint E k
  disjoint k n
  disjoint k z
  disjoint E m
  disjoint m n
  disjoint O k
  disjoint O m
  disjoint Z k
  disjoint Z m
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. z e. ( ~P Z i^i Fin ) ( O ` U_ n e. Z ( E ` n ) ) < ( sum_ n e. z ( O ` ( E ` n ) ) + Y ) )

  proof
    wph
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    vn
    cZ
    @1
    ciun
    #
    cO
    cfv
    #
    vz
    cv
    #
    @2
    vn
    csu
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vz
    cZ
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wph
    @5
    wa
    #
    @7
    @3
    @8
    cres
    #
    csumge0
    cfv
    #
    clt
    wbr
    #
    vz
    @13
    wrex
    @14
    @15
    vz
    @3
    cvv
    cZ
    @7
    cZ
    cvv
    wcel
    #
    @15
    cZ
    cN
    cuz
    cfv
    cvv
    omeiunltfirp.z
    cN
    cuz
    fvex
    eqeltri
    #
    a1i
    wph
    cZ
    cc0
    cpnf
    cicc
    co
    #
    @3
    wf
    @5
    wph
    vn
    cZ
    @2
    @21
    @3
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    cO
    cX
    wph
    cO
    come
    wcel
    #
    @22
    omeiunltfirp.o
    adantr
    omeiunltfirp.x
    @23
    @1
    cX
    cpw
    #
    wcel
    #
    @1
    cX
    wss
    #
    wph
    cZ
    @25
    @0
    cE
    omeiunltfirp.e
    ffvelrnda
    @1
    cX
    @0
    cE
    fvex
    elpw
    #
    sylib
    #
    omecl
    #
    @3
    eqid
    fmptd
    #
    adantr
    wph
    @5
    simpr
    wph
    @7
    cr
    wcel
    #
    @5
    omeiunltfirp.re
    adantr
    sge0pnffigt
    @15
    @18
    @11
    vz
    @13
    wph
    @8
    @13
    wcel
    #
    @18
    @11
    wi
    @5
    wph
    @33
    wa
    #
    @18
    @11
    @34
    @18
    wa
    @34
    @7
    vn
    @8
    @2
    cmpt
    #
    csumge0
    cfv
    #
    clt
    wbr
    #
    @11
    @34
    @18
    simpl
    @33
    @18
    @37
    wph
    @33
    @18
    wa
    @7
    @17
    @36
    clt
    @33
    @18
    simpr
    @33
    @17
    @36
    wceq
    @18
    @33
    @16
    @35
    csumge0
    @33
    vn
    cZ
    @8
    @2
    @8
    cZ
    cfn
    elpwinss
    #
    resmptd
    fveq2d
    adantr
    breqtrd
    adantll
    @34
    @37
    wa
    @7
    @36
    @10
    wph
    @7
    cxr
    wcel
    @33
    @37
    wph
    @7
    omeiunltfirp.re
    rexrd
    ad2antrr
    @34
    @36
    cxr
    wcel
    @37
    @34
    @35
    @13
    @8
    wph
    @33
    simpr
    @34
    vn
    @8
    @2
    @21
    @35
    @34
    @0
    @8
    wcel
    #
    wa
    #
    @1
    cO
    cX
    wph
    @24
    @33
    @39
    omeiunltfirp.o
    ad2antrr
    #
    omeiunltfirp.x
    @40
    @26
    @27
    @40
    cZ
    @25
    @0
    cE
    wph
    cZ
    @25
    cE
    wf
    @33
    @39
    omeiunltfirp.e
    ad2antrr
    @33
    @39
    @22
    wph
    @33
    @39
    wa
    @8
    cZ
    @0
    @33
    @8
    cZ
    wss
    @39
    @38
    adantr
    @33
    @39
    simpr
    sseldd
    adantll
    #
    ffvelrnd
    @28
    sylib
    #
    omecl
    #
    @35
    eqid
    #
    fmptd
    sge0xrcl
    adantr
    @34
    @10
    cxr
    wcel
    @37
    @34
    @10
    @34
    @9
    cY
    @34
    @8
    @2
    vn
    @33
    @8
    cfn
    wcel
    #
    wph
    @8
    @12
    cfn
    elinel2
    #
    adantl
    #
    @40
    cc0
    cpnf
    cico
    co
    #
    cr
    @2
    rge0ssre
    @40
    cc0
    cpnf
    @2
    cc0
    cxr
    wcel
    #
    @40
    0xr
    a1i
    #
    cpnf
    cxr
    wcel
    #
    @40
    pnfxr
    a1i
    #
    @40
    @1
    cO
    cX
    @41
    omeiunltfirp.x
    @43
    omexrcl
    #
    @40
    @50
    @52
    @2
    @21
    wcel
    #
    cc0
    @2
    cle
    wbr
    @51
    @53
    @44
    cc0
    cpnf
    @2
    iccgelb
    syl3anc
    @40
    @2
    @7
    cpnf
    @54
    @40
    @6
    cO
    cX
    @41
    omeiunltfirp.x
    wph
    @6
    cX
    wss
    #
    @33
    @39
    wph
    @27
    vn
    cZ
    wral
    @56
    wph
    @27
    vn
    cZ
    @29
    ralrimiva
    vn
    cZ
    @1
    cX
    iunss
    sylibr
    ad2antrr
    #
    omexrcl
    @53
    @40
    @1
    @6
    cO
    cX
    @41
    omeiunltfirp.x
    @57
    @40
    @22
    @1
    @6
    wss
    @42
    vn
    cZ
    @1
    ssiun2
    syl
    omessle
    wph
    @7
    cpnf
    clt
    wbr
    @33
    @39
    wph
    @7
    omeiunltfirp.re
    ltpnfd
    ad2antrr
    xrlelttrd
    elicod
    #
    sseldi
    fsumrecl
    #
    wph
    cY
    cr
    wcel
    @33
    wph
    cY
    omeiunltfirp.y
    rpred
    adantr
    readdcld
    #
    rexrd
    adantr
    @34
    @37
    simpr
    @34
    @36
    @10
    clt
    wbr
    @37
    @34
    @36
    @9
    @10
    clt
    @34
    @36
    @8
    vk
    cv
    #
    @35
    cfv
    #
    vk
    csu
    @8
    @61
    cE
    cfv
    #
    cO
    cfv
    #
    vk
    csu
    #
    @9
    @34
    vk
    @35
    @8
    @48
    @34
    vn
    @8
    @2
    @49
    @35
    @58
    @45
    fmptd
    sge0fsum
    @34
    @8
    @62
    @64
    vk
    @34
    @61
    @8
    wcel
    #
    wa
    #
    vn
    @61
    @2
    @64
    @8
    @35
    cvv
    @67
    @35
    eqidd
    @0
    @61
    wceq
    #
    @2
    @64
    wceq
    @67
    @68
    @1
    @63
    cO
    @0
    @61
    cE
    fveq2
    fveq2d
    adantl
    @34
    @66
    simpr
    @67
    @63
    cO
    fvexd
    fvmptd
    sumeq2dv
    @65
    @9
    wceq
    @34
    @8
    @64
    @2
    vk
    vn
    @61
    @0
    wceq
    @63
    @1
    cO
    @61
    @0
    cE
    fveq2
    fveq2d
    cbvsumv
    a1i
    3eqtrd
    @34
    @9
    cY
    @59
    wph
    cY
    crp
    wcel
    #
    @33
    omeiunltfirp.y
    adantr
    ltaddrpd
    eqbrtrd
    adantr
    xrlttrd
    syl2anc
    ex
    adantlr
    reximdva
    mpd
    wph
    @5
    wn
    #
    wa
    #
    wph
    @4
    cr
    wcel
    #
    @14
    wph
    @70
    simpl
    @71
    @72
    @70
    wph
    @70
    simpr
    wph
    @72
    @70
    wb
    @70
    wph
    @3
    cvv
    cZ
    @19
    wph
    @20
    a1i
    @31
    sge0repnf
    adantr
    mpbird
    wph
    @72
    wa
    #
    @4
    @36
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vz
    @13
    wrex
    @14
    @73
    vn
    vz
    cZ
    @2
    cvv
    cY
    wph
    @72
    vn
    wph
    vn
    nfv
    #
    vn
    @4
    cr
    vn
    @3
    csumge0
    vn
    csumge0
    nfcv
    vn
    cZ
    @2
    nfmpt1
    nffv
    vn
    cr
    nfcv
    nfel
    nfan
    @19
    @73
    @20
    a1i
    wph
    @22
    @55
    @72
    @30
    adantlr
    wph
    @69
    @72
    omeiunltfirp.y
    adantr
    wph
    @72
    simpr
    #
    sge0ltfirpmpt
    @73
    @75
    @11
    vz
    @13
    @73
    @33
    wa
    #
    @75
    @11
    @78
    @75
    wa
    #
    @7
    @4
    @10
    wph
    @32
    @72
    @33
    @75
    omeiunltfirp.re
    ad3antrrr
    @73
    @72
    @33
    @75
    @77
    ad2antrr
    wph
    @33
    @10
    cr
    wcel
    @72
    @75
    @60
    ad4ant13
    wph
    @7
    @4
    cle
    wbr
    @72
    @33
    @75
    wph
    vn
    cE
    cN
    cO
    cX
    cZ
    @76
    vn
    cE
    nfcv
    omeiunltfirp.o
    omeiunltfirp.x
    omeiunltfirp.z
    omeiunltfirp.e
    omeiunle
    ad3antrrr
    @79
    @4
    @74
    @10
    clt
    @78
    @75
    simpr
    @78
    @74
    @10
    wceq
    @75
    @78
    @36
    @9
    cY
    caddc
    @78
    wph
    vm
    cZ
    vm
    cv
    #
    cE
    cfv
    #
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cr
    wcel
    #
    @33
    @36
    @9
    wceq
    wph
    @72
    @33
    simpll
    @72
    @85
    wph
    @33
    @72
    @85
    @4
    @84
    cr
    @3
    @83
    csumge0
    vn
    vm
    cZ
    @2
    @82
    @0
    @80
    wceq
    @1
    @81
    cO
    @0
    @80
    cE
    fveq2
    fveq2d
    cbvmptv
    fveq2i
    eleq1i
    biimpi
    ad2antlr
    @73
    @33
    simpr
    wph
    @85
    wa
    #
    @33
    wa
    @8
    @2
    vn
    @33
    @46
    @86
    @47
    adantl
    wph
    @33
    @39
    @2
    @49
    wcel
    @85
    @58
    adantllr
    sge0fsummpt
    syl21anc
    oveq1d
    adantr
    breqtrd
    lelttrd
    ex
    reximdva
    mpd
    syl2anc
    pm2.61dan
end
