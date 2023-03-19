include "wss.mm"
include "wcel.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wun0.mm"
include "a1d.mm"
include "ssun1.mm"
include "sstr.mm"
include "mpan.mm"
include "imim1i.mm"
include "wa.mm"
include "cwun.mm"
include "adantr.mm"
include "simprr.mm"
include "simprl.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "wunsn.mm"
include "wunun.mm"
include "exp32.mm"
include "a2d.mm"
include "syl5.mm"
include "a2i.mm"
include "a1i.mm"
include "findcard2.mm"
include "mpcom.mm"
include "mpd.mm"

theorem wunfi
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunfi.2: |- ( ph -> A C_ U )
  assume wunfi.3: |- ( ph -> A e. Fin )


  assert |- ( ph -> A e. U )

  proof
    wph
    cA
    cU
    wss
    #
    cA
    cU
    wcel
    #
    wunfi.2
    cA
    cfn
    wcel
    wph
    @0
    @1
    wi
    #
    wunfi.3
    wph
    vx
    cv
    #
    cU
    wss
    #
    @3
    cU
    wcel
    #
    wi
    #
    wi
    wph
    c0
    cU
    wss
    #
    c0
    cU
    wcel
    #
    wi
    #
    wi
    wph
    vy
    cv
    #
    cU
    wss
    #
    @10
    cU
    wcel
    #
    wi
    #
    wi
    #
    wph
    @10
    vz
    cv
    #
    csn
    #
    cun
    #
    cU
    wss
    #
    @17
    cU
    wcel
    #
    wi
    #
    wi
    #
    wph
    @2
    wi
    vx
    vy
    vz
    cA
    @3
    c0
    wceq
    #
    @6
    @9
    wph
    @22
    @4
    @7
    @5
    @8
    @3
    c0
    cU
    sseq1
    @3
    c0
    cU
    eleq1
    imbi12d
    imbi2d
    @3
    @10
    wceq
    #
    @6
    @13
    wph
    @23
    @4
    @11
    @5
    @12
    @3
    @10
    cU
    sseq1
    @3
    @10
    cU
    eleq1
    imbi12d
    imbi2d
    @3
    @17
    wceq
    #
    @6
    @20
    wph
    @24
    @4
    @18
    @5
    @19
    @3
    @17
    cU
    sseq1
    @3
    @17
    cU
    eleq1
    imbi12d
    imbi2d
    @3
    cA
    wceq
    #
    @6
    @2
    wph
    @25
    @4
    @0
    @5
    @1
    @3
    cA
    cU
    sseq1
    @3
    cA
    cU
    eleq1
    imbi12d
    imbi2d
    wph
    @8
    @7
    wph
    cU
    wun0.1
    wun0
    a1d
    @14
    @21
    wi
    @10
    cfn
    wcel
    wph
    @13
    @20
    @13
    @18
    @12
    wi
    wph
    @20
    @18
    @11
    @12
    @10
    @17
    wss
    @18
    @11
    @10
    @16
    ssun1
    @10
    @17
    cU
    sstr
    mpan
    imim1i
    wph
    @18
    @12
    @19
    wph
    @18
    @12
    @19
    wph
    @18
    @12
    wa
    #
    wa
    #
    @10
    @16
    cU
    wph
    cU
    cwun
    wcel
    @26
    wun0.1
    adantr
    #
    wph
    @18
    @12
    simprr
    @27
    @15
    cU
    @28
    @27
    @16
    cU
    wss
    @15
    cU
    wcel
    @27
    @10
    @16
    cU
    wph
    @18
    @12
    simprl
    unssbd
    @15
    cU
    vz
    vex
    snss
    sylibr
    wunsn
    wunun
    exp32
    a2d
    syl5
    a2i
    a1i
    findcard2
    mpcom
    mpd
end
