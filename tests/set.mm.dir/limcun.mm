include "climc.mm"
include "co.mm"
include "cres.mm"
include "cin.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "limcrcl.mm"
include "simp3d.mm"
include "a1i.mm"
include "inss1.mm"
include "sseli.mm"
include "syl.mm"
include "wb.mm"
include "wa.mm"
include "cpr.mm"
include "ciin.mm"
include "cfn.mm"
include "prfi.mm"
include "wral.mm"
include "adantr.mm"
include "cvv.mm"
include "cnex.mm"
include "ssex.mm"
include "sseq1.mm"
include "ralprg.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ciun.mm"
include "cun.mm"
include "cuni.mm"
include "uniiun.mm"
include "wceq.mm"
include "uniprg.mm"
include "syl5eqr.mm"
include "feq2d.mm"
include "mpbird.mm"
include "simpr.mm"
include "limciun.mm"
include "eleq2d.mm"
include "reseq2.mm"
include "oveq1d.mm"
include "anbi2d.mm"
include "limccl.mm"
include "pm4.71ri.mm"
include "syl6bbr.mm"
include "elriin.mm"
include "elin.mm"
include "3bitr4g.mm"
include "bitrd.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem limcun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume limcun.1: |- ( ph -> A C_ CC )
  assume limcun.2: |- ( ph -> B C_ CC )
  assume limcun.3: |- ( ph -> F : ( A u. B ) --> CC )


  assert |- ( ph -> ( F limCC C ) = ( ( ( F |` A ) limCC C ) i^i ( ( F |` B ) limCC C ) ) )

  proof
    wph
    vx
    cF
    cC
    climc
    co
    #
    cF
    cA
    cres
    #
    cC
    climc
    co
    #
    cF
    cB
    cres
    #
    cC
    climc
    co
    #
    cin
    #
    wph
    cC
    cc
    wcel
    #
    vx
    cv
    #
    @0
    wcel
    #
    @7
    @5
    wcel
    #
    @8
    @6
    wi
    wph
    @8
    cF
    cdm
    #
    cc
    cF
    wf
    @10
    cc
    wss
    @6
    cC
    @7
    cF
    limcrcl
    simp3d
    a1i
    @9
    @6
    wi
    wph
    @9
    @7
    @2
    wcel
    #
    @6
    @5
    @2
    @7
    @2
    @4
    inss1
    sseli
    @11
    @1
    cdm
    #
    cc
    @1
    wf
    @12
    cc
    wss
    @6
    cC
    @7
    @1
    limcrcl
    simp3d
    syl
    a1i
    wph
    @6
    @8
    @9
    wb
    wph
    @6
    wa
    #
    @8
    @7
    cc
    vy
    cA
    cB
    cpr
    #
    cF
    vy
    cv
    #
    cres
    #
    cC
    climc
    co
    #
    ciin
    cin
    #
    wcel
    #
    @9
    @13
    @0
    @18
    @7
    @13
    vy
    @14
    @15
    cC
    cF
    @14
    cfn
    wcel
    @13
    cA
    cB
    prfi
    a1i
    @13
    @15
    cc
    wss
    #
    vy
    @14
    wral
    #
    cA
    cc
    wss
    #
    cB
    cc
    wss
    #
    wph
    @22
    @6
    limcun.1
    adantr
    #
    wph
    @23
    @6
    limcun.2
    adantr
    #
    @13
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @21
    @22
    @23
    wa
    wb
    @13
    @22
    @26
    @24
    cA
    cc
    cnex
    ssex
    syl
    #
    @13
    @23
    @27
    @25
    cB
    cc
    cnex
    ssex
    syl
    #
    @20
    @22
    @23
    vy
    cA
    cB
    cvv
    cvv
    @15
    cA
    cc
    sseq1
    @15
    cB
    cc
    sseq1
    ralprg
    syl2anc
    mpbir2and
    @13
    vy
    @14
    @15
    ciun
    #
    cc
    cF
    wf
    cA
    cB
    cun
    #
    cc
    cF
    wf
    #
    wph
    @32
    @6
    limcun.3
    adantr
    @13
    @30
    @31
    cc
    cF
    @13
    @30
    @14
    cuni
    #
    @31
    vy
    @14
    uniiun
    @13
    @26
    @27
    @33
    @31
    wceq
    @28
    @29
    cA
    cB
    cvv
    cvv
    uniprg
    syl2anc
    syl5eqr
    feq2d
    mpbird
    wph
    @6
    simpr
    limciun
    eleq2d
    @13
    @7
    cc
    wcel
    #
    @7
    @17
    wcel
    #
    vy
    @14
    wral
    #
    wa
    #
    @11
    @7
    @4
    wcel
    #
    wa
    #
    @19
    @9
    @13
    @37
    @34
    @39
    wa
    @39
    @13
    @36
    @39
    @34
    @13
    @26
    @27
    @36
    @39
    wb
    @28
    @29
    @35
    @11
    @38
    vy
    cA
    cB
    cvv
    cvv
    @15
    cA
    wceq
    #
    @17
    @2
    @7
    @40
    @16
    @1
    cC
    climc
    @15
    cA
    cF
    reseq2
    oveq1d
    eleq2d
    @15
    cB
    wceq
    #
    @17
    @4
    @7
    @41
    @16
    @3
    cC
    climc
    @15
    cB
    cF
    reseq2
    oveq1d
    eleq2d
    ralprg
    syl2anc
    anbi2d
    @39
    @34
    @11
    @34
    @38
    @2
    cc
    @7
    cC
    @1
    limccl
    sseli
    adantr
    pm4.71ri
    syl6bbr
    vy
    cc
    @7
    @17
    @14
    elriin
    @7
    @2
    @4
    elin
    3bitr4g
    bitrd
    ex
    pm5.21ndd
    eqrdv
end
