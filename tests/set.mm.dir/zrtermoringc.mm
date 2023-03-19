include "ctermo.mm"
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
include "crh.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "crg.mm"
include "cnzr.mm"
include "cdif.mm"
include "cin.mm"
include "eqid.mm"
include "ringcbas.mm"
include "eleq2d.mm"
include "elin.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "imp.mm"
include "adantr.mm"
include "c0rhm.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eldifad.mm"
include "elind.mm"
include "eleqtrrd.mm"
include "ringchom.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "wf.mm"
include "rhmf.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "fvex.mm"
include "fnmpti.mm"
include "a1i.mm"
include "csn.mm"
include "0ringbas.mm"
include "syl.mm"
include "feq3d.mm"
include "fvconst.mm"
include "ex.mm"
include "imp31.mm"
include "cvv.mm"
include "eqidd.mm"
include "id.mm"
include "fvmptd.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"
include "syld.mm"
include "alrimiv.mm"
include "3jca.mm"
include "mpdan.mm"
include "eleq1.mm"
include "eqeu.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "ringccat.mm"
include "istermo.mm"
include "mpbird.mm"

theorem zrtermoringc
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
  assume zrtermoringc.u: |- ( ph -> U e. V )
  assume zrtermoringc.c: |- C = ( RingCat ` U )
  assume zrtermoringc.z: |- ( ph -> Z e. ( Ring \ NzRing ) )
  assume zrtermoringc.e: |- ( ph -> Z e. U )


  assert |- ( ph -> Z e. ( TermO ` C ) )

  proof
    wph
    cZ
    cC
    ctermo
    cfv
    wcel
    vh
    cv
    #
    vr
    cv
    #
    cZ
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
    @1
    cbs
    cfv
    #
    cZ
    c0g
    cfv
    #
    cmpt
    #
    @1
    cZ
    crh
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
    crg
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
    crg
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
    zrtermoringc.c
    @6
    eqid
    #
    zrtermoringc.u
    ringcbas
    #
    eleq2d
    @22
    @1
    cU
    wcel
    @19
    @1
    cU
    crg
    elin
    simprbi
    syl6bi
    imp
    wph
    @20
    @7
    zrtermoringc.z
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
    c0rhm
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
    @1
    cZ
    zrtermoringc.c
    @23
    wph
    cU
    cV
    wcel
    #
    @7
    zrtermoringc.u
    adantr
    @2
    eqid
    #
    wph
    @7
    simpr
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
    crg
    cZ
    zrtermoringc.e
    wph
    cZ
    crg
    cnzr
    zrtermoringc.z
    eldifad
    elind
    @24
    eleqtrrd
    #
    adantr
    ringchom
    #
    eqcomd
    eleq2d
    biimpa
    @28
    @16
    vh
    @28
    @4
    @9
    cZ
    cbs
    cfv
    #
    @0
    wf
    #
    @15
    @8
    @4
    @34
    wi
    @13
    @8
    @4
    @0
    @12
    wcel
    @34
    @8
    @3
    @12
    @0
    @32
    eleq2d
    @9
    @33
    @1
    cZ
    @0
    @25
    @33
    eqid
    #
    rhmf
    syl6bi
    adantr
    @28
    @34
    @15
    @28
    @34
    wa
    #
    va
    @9
    @0
    @11
    @34
    @0
    @9
    wfn
    @28
    @9
    @33
    @0
    ffn
    adantl
    @11
    @9
    wfn
    @36
    vx
    @9
    @10
    @11
    cZ
    c0g
    fvex
    #
    @27
    fnmpti
    a1i
    @36
    va
    cv
    #
    @9
    wcel
    #
    wa
    @38
    @0
    cfv
    #
    @10
    @38
    @11
    cfv
    #
    @28
    @34
    @39
    @40
    @10
    wceq
    #
    @8
    @34
    @39
    @42
    wi
    #
    wi
    @13
    @8
    @34
    @9
    @10
    csn
    #
    @0
    wf
    #
    @43
    @8
    @33
    @44
    @0
    @9
    wph
    @33
    @44
    wceq
    #
    @7
    wph
    @20
    @46
    zrtermoringc.z
    @33
    cZ
    @10
    @35
    @26
    0ringbas
    syl
    adantr
    feq3d
    @45
    @39
    @42
    @9
    @10
    @38
    @0
    fvconst
    ex
    syl6bi
    adantr
    imp31
    @39
    @41
    @10
    wceq
    @36
    @39
    vx
    @38
    @10
    @10
    @9
    @11
    cvv
    @39
    @11
    eqidd
    @39
    vx
    cv
    @38
    wceq
    wa
    @10
    eqidd
    @39
    id
    @10
    cvv
    wcel
    @39
    @37
    a1i
    fvmptd
    adantl
    eqtr4d
    eqfnfvd
    ex
    syld
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
    zrtermoringc.u
    cC
    cU
    cV
    zrtermoringc.c
    ringccat
    syl
    @31
    istermo
    mpbird
end
