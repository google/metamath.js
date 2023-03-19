include "ceu.mm"
include "cc.mm"
include "caa.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "1red.mm"
include "cr.mm"
include "nn0abscl.mm"
include "nn0red.mm"
include "adantr.mm"
include "nnabscl.mm"
include "nnge1d.mm"
include "lensymd.mm"
include "nan.mm"
include "mpbir.mm"
include "nrex.mm"
include "ccoe.mm"
include "wceq.mm"
include "cply.mm"
include "csn.mm"
include "ere.mm"
include "recni.mm"
include "neldif.mm"
include "mpan.mm"
include "ene0.mm"
include "wb.mm"
include "elsng.mm"
include "ax-mp.mm"
include "nemtbir.mm"
include "a1i.mm"
include "eldifd.mm"
include "elaa2.mm"
include "sylib.mm"
include "simprd.mm"
include "cdgr.mm"
include "cfz.mm"
include "co.mm"
include "ccxp.mm"
include "cmul.mm"
include "caddc.mm"
include "cexp.mm"
include "csu.mm"
include "cn0.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cuz.mm"
include "wral.mm"
include "crab.mm"
include "cinf.mm"
include "ctp.mm"
include "cxr.mm"
include "csup.mm"
include "c0p.mm"
include "simpl.mm"
include "0nn0.mm"
include "n0p.mm"
include "mp3an2.mm"
include "nelsn.mm"
include "syl.mm"
include "adantrr.mm"
include "simprr.mm"
include "eqid.mm"
include "simprl.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cbvsumv.mm"
include "cbvmptv.mm"
include "id.mm"
include "fveq12d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "raleqdv.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "infeq1i.mm"
include "etransclem48.mm"
include "rexlimiva.mm"
include "mt3.mm"

theorem etransc
  let vh: setvar h
  let vi: setvar i
  let vl: setvar l
  let vn: setvar n
  let vq: setvar q
  let vk: setvar k
  let vj: setvar j
  let vm: setvar m
  let vx: setvar x


  assert |- _e e. ( CC \ AA )

  proof
    ceu
    cc
    caa
    cdif
    wcel
    #
    vk
    cv
    #
    cc0
    wne
    #
    @1
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    vk
    cz
    wrex
    #
    @5
    vk
    cz
    @1
    cz
    wcel
    #
    @5
    wn
    wi
    @7
    @2
    wa
    #
    @4
    wn
    wi
    @8
    c1
    @3
    @8
    1red
    @7
    @3
    cr
    wcel
    @2
    @7
    @3
    @1
    nn0abscl
    nn0red
    adantr
    @8
    @3
    @1
    nnabscl
    nnge1d
    lensymd
    @7
    @2
    @4
    nan
    mpbir
    nrex
    @0
    wn
    #
    cc0
    vq
    cv
    #
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    ceu
    @10
    cfv
    cc0
    wceq
    #
    wa
    #
    vq
    cz
    cply
    cfv
    #
    wrex
    #
    @6
    @9
    ceu
    cc
    wcel
    #
    @17
    @9
    ceu
    caa
    cc0
    csn
    #
    cdif
    wcel
    @18
    @17
    wa
    @9
    ceu
    caa
    @19
    @18
    @9
    ceu
    caa
    wcel
    ceu
    ere
    recni
    #
    ceu
    cc
    caa
    neldif
    mpan
    ceu
    @19
    wcel
    #
    wn
    @9
    @21
    ceu
    cc0
    ene0
    @18
    @21
    ceu
    cc0
    wceq
    wb
    @20
    ceu
    cc0
    cc
    elsng
    ax-mp
    nemtbir
    a1i
    eldifd
    ceu
    vq
    elaa2
    sylib
    simprd
    @15
    @6
    vq
    @16
    @10
    @16
    wcel
    #
    @15
    wa
    @11
    cc0
    @10
    cdgr
    cfv
    #
    cfz
    co
    #
    vl
    cv
    #
    @11
    cfv
    #
    ceu
    @25
    ccxp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @23
    @23
    @23
    c1
    caddc
    co
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    vl
    csu
    #
    @10
    vn
    cn0
    @33
    @30
    vn
    cv
    #
    cexp
    co
    #
    @34
    cfa
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    @12
    cabs
    cfv
    @23
    cfa
    cfv
    vm
    cv
    #
    vm
    cn0
    @24
    vh
    cv
    #
    @11
    cfv
    #
    ceu
    @41
    ccxp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @31
    cmul
    co
    #
    vh
    csu
    #
    @30
    @40
    cexp
    co
    #
    @40
    cfa
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vm
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn0
    crab
    #
    cr
    clt
    cinf
    #
    ctp
    cxr
    clt
    csup
    #
    vi
    vl
    vk
    vn
    @60
    @23
    @22
    @13
    @10
    @16
    c0p
    csn
    #
    cdif
    wcel
    @14
    @22
    @13
    wa
    #
    @10
    @16
    @62
    @22
    @13
    simpl
    @63
    @10
    c0p
    wne
    #
    @10
    @62
    wcel
    wn
    @22
    cc0
    cn0
    wcel
    @13
    @64
    0nn0
    @10
    cc0
    n0p
    mp3an2
    @10
    c0p
    nelsn
    syl
    eldifd
    adantrr
    @22
    @13
    @14
    simprr
    @11
    eqid
    @22
    @13
    @14
    simprl
    @23
    eqid
    @33
    eqid
    @39
    eqid
    cr
    @59
    @34
    @39
    cfv
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vn
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vi
    cn0
    crab
    clt
    @58
    @70
    vj
    vi
    cn0
    @58
    @67
    vn
    @57
    wral
    @56
    @68
    wceq
    #
    @70
    @55
    @67
    vm
    vn
    @57
    @40
    @34
    wceq
    #
    @54
    @66
    c1
    clt
    @72
    @53
    @65
    cabs
    @72
    @40
    @34
    @52
    @39
    @52
    @39
    wceq
    @72
    vm
    vn
    cn0
    @51
    @38
    @72
    @47
    @33
    @50
    @37
    cmul
    @47
    @33
    wceq
    @72
    @24
    @46
    @32
    vh
    vl
    @41
    @25
    wceq
    #
    @45
    @29
    @31
    cmul
    @73
    @44
    @28
    cabs
    @73
    @42
    @26
    @43
    @27
    cmul
    @41
    @25
    @11
    fveq2
    @41
    @25
    ceu
    ccxp
    oveq2
    oveq12d
    fveq2d
    oveq1d
    cbvsumv
    a1i
    @72
    @48
    @35
    @49
    @36
    cdiv
    @40
    @34
    @30
    cexp
    oveq2
    @40
    @34
    cfa
    fveq2
    oveq12d
    oveq12d
    cbvmptv
    a1i
    @72
    id
    fveq12d
    fveq2d
    breq1d
    cbvralv
    @71
    @67
    vn
    @57
    @69
    @56
    @68
    cuz
    fveq2
    raleqdv
    syl5bb
    cbvrabv
    infeq1i
    @61
    eqid
    etransclem48
    rexlimiva
    syl
    mt3
end
