include "cinito.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "weu.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "c0g.mm"
include "cmpt.mm"
include "crngh.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "crng.mm"
include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "cin.mm"
include "eqid.mm"
include "rngcbas.mm"
include "eleq2d.mm"
include "elin.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "imp.mm"
include "adantr.mm"
include "zrrnghm.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eldifi.mm"
include "ringrng.mm"
include "3syl.mm"
include "elind.mm"
include "eleqtrrd.mm"
include "rngchom.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "wf.mm"
include "rnghmf.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "fvex.mm"
include "fnmpti.mm"
include "a1i.mm"
include "cghm.mm"
include "rnghmghm.mm"
include "ghmid.mm"
include "ad2antrr.mm"
include "csn.mm"
include "0ringbas.mm"
include "syl.mm"
include "elsni.mm"
include "fveq2d.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "id.mm"
include "fvmptd.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "mpdan.mm"
include "ex.mm"
include "alrimiv.mm"
include "3jca.mm"
include "eleq1.mm"
include "eqeu.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "rngccat.mm"
include "isinito.mm"
include "mpbird.mm"

theorem zrinitorngc
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vh: setvar h
  let vr: setvar r
  let vx: setvar x
  let vk: setvar k
  assume zrinitorngc.u: |- ( ph -> U e. V )
  assume zrinitorngc.c: |- C = ( RngCat ` U )
  assume zrinitorngc.z: |- ( ph -> Z e. ( Ring \ NzRing ) )
  assume zrinitorngc.e: |- ( ph -> Z e. U )


  assert |- ( ph -> Z e. ( InitO ` C ) )

  proof
    wph
    cZ
    cC
    cinito
    cfv
    wcel
    vh
    cv
    #
    cZ
    vr
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    vh
    weu
    #
    vr
    cC
    cbs
    cfv
    #
    wral
    wph
    @5
    vr
    @6
    wph
    @1
    @6
    wcel
    #
    wa
    #
    vx
    cZ
    cbs
    cfv
    #
    @1
    c0g
    cfv
    #
    cmpt
    #
    cZ
    @1
    crngh
    co
    #
    wcel
    #
    @11
    @3
    wcel
    #
    @4
    @0
    @11
    wceq
    #
    wi
    #
    vh
    wal
    #
    w3a
    #
    @5
    @8
    @13
    @18
    @8
    @1
    crng
    wcel
    #
    cZ
    crg
    cnzr
    cdif
    wcel
    #
    @13
    wph
    @7
    @19
    wph
    @7
    @1
    cU
    crng
    cin
    #
    wcel
    #
    @19
    wph
    @6
    @21
    @1
    wph
    @6
    cC
    cU
    cV
    zrinitorngc.c
    @6
    eqid
    #
    zrinitorngc.u
    rngcbas
    #
    eleq2d
    @22
    @1
    cU
    wcel
    @19
    @1
    cU
    crng
    elin
    simprbi
    syl6bi
    imp
    wph
    @20
    @7
    zrinitorngc.z
    adantr
    vx
    @9
    @1
    cZ
    @11
    @10
    @9
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    zrrnghm
    syl2anc
    @8
    @13
    wa
    #
    @13
    @14
    @17
    @8
    @13
    simpr
    @8
    @13
    @14
    @8
    @12
    @3
    @11
    @8
    @3
    @12
    @8
    @6
    cC
    cU
    @2
    cV
    cZ
    @1
    zrinitorngc.c
    @23
    wph
    cU
    cV
    wcel
    #
    @7
    zrinitorngc.u
    adantr
    @2
    eqid
    #
    wph
    cZ
    @6
    wcel
    @7
    wph
    cZ
    @21
    @6
    wph
    cU
    crng
    cZ
    zrinitorngc.e
    wph
    @20
    cZ
    crg
    wcel
    cZ
    crng
    wcel
    zrinitorngc.z
    cZ
    crg
    cnzr
    eldifi
    cZ
    ringrng
    3syl
    elind
    @24
    eleqtrrd
    #
    adantr
    wph
    @7
    simpr
    rngchom
    #
    eqcomd
    eleq2d
    biimpa
    @28
    @16
    vh
    @8
    @16
    @13
    @8
    @4
    @15
    @8
    @4
    wa
    #
    @9
    @1
    cbs
    cfv
    #
    @0
    wf
    #
    @15
    @8
    @4
    @35
    @8
    @4
    @0
    @12
    wcel
    #
    @35
    @8
    @3
    @12
    @0
    @32
    eleq2d
    #
    @9
    @34
    cZ
    @1
    @0
    @25
    @34
    eqid
    rnghmf
    syl6bi
    imp
    @33
    @35
    wa
    #
    va
    @9
    @0
    @11
    @35
    @0
    @9
    wfn
    @33
    @9
    @34
    @0
    ffn
    adantl
    @11
    @9
    wfn
    @38
    vx
    @9
    @10
    @11
    @1
    c0g
    fvex
    #
    @27
    fnmpti
    a1i
    @38
    va
    cv
    #
    @9
    wcel
    #
    wa
    cZ
    c0g
    cfv
    #
    @0
    cfv
    #
    @10
    @40
    @0
    cfv
    #
    @40
    @11
    cfv
    #
    @33
    @43
    @10
    wceq
    #
    @35
    @41
    @33
    @36
    @0
    cZ
    @1
    cghm
    co
    wcel
    @46
    @8
    @4
    @36
    @37
    biimpa
    cZ
    @1
    @0
    rnghmghm
    cZ
    @1
    @0
    @42
    @10
    @42
    eqid
    #
    @26
    ghmid
    3syl
    ad2antrr
    @38
    @41
    @44
    @43
    wceq
    #
    @8
    @41
    @48
    wi
    #
    @4
    @35
    wph
    @49
    @7
    wph
    @41
    @40
    @42
    csn
    #
    wcel
    #
    @48
    wph
    @9
    @50
    @40
    wph
    @20
    @9
    @50
    wceq
    zrinitorngc.z
    @9
    cZ
    @42
    @25
    @47
    0ringbas
    syl
    eleq2d
    @51
    @40
    @42
    @0
    @40
    @42
    elsni
    fveq2d
    syl6bi
    adantr
    ad2antrr
    imp
    @41
    @45
    @10
    wceq
    @38
    @41
    vx
    @40
    @10
    @10
    @9
    @11
    cvv
    @41
    @11
    eqidd
    @41
    vx
    va
    weq
    wa
    @10
    eqidd
    @41
    id
    @10
    cvv
    wcel
    @41
    @39
    a1i
    fvmptd
    adantl
    3eqtr4d
    eqfnfvd
    mpdan
    ex
    adantr
    alrimiv
    3jca
    mpdan
    @4
    @14
    vh
    @11
    @12
    @0
    @11
    @3
    eleq1
    eqeu
    syl
    ralrimiva
    wph
    @6
    cC
    vh
    @2
    cZ
    vr
    @23
    @30
    wph
    @29
    cC
    ccat
    wcel
    zrinitorngc.u
    cC
    cU
    cV
    zrinitorngc.c
    rngccat
    syl
    @31
    isinito
    mpbird
end
