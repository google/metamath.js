include "cr1.mm"
include "com.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "r10.mm"
include "wun0.mm"
include "syl5eqel.mm"
include "wa.mm"
include "cpw.mm"
include "cwun.mm"
include "adantr.mm"
include "simpr.mm"
include "wunpw.mm"
include "con0.mm"
include "nnon.mm"
include "r1suc.mm"
include "syl.mm"
include "syl5ibr.mm"
include "expd.mm"
include "finds2.mm"
include "eleq1.mm"
include "imbi2d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "wfun.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvelima.mm"
include "mpan.mm"
include "syl11.mm"
include "ssrdv.mm"

theorem wunr1om
  let wph: wff ph
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume wun0.1: |- ( ph -> U e. WUni )


  assert |- ( ph -> ( R1 " _om ) C_ U )

  proof
    wph
    vy
    cr1
    com
    cima
    #
    cU
    vx
    cv
    #
    cr1
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vx
    com
    wrex
    #
    wph
    @3
    cU
    wcel
    #
    @3
    @0
    wcel
    #
    @4
    wph
    @6
    wi
    #
    vx
    com
    @1
    com
    wcel
    wph
    @2
    cU
    wcel
    #
    wi
    @4
    @8
    @9
    c0
    cr1
    cfv
    #
    cU
    wcel
    @3
    cr1
    cfv
    #
    cU
    wcel
    #
    @3
    csuc
    #
    cr1
    cfv
    #
    cU
    wcel
    #
    wph
    vx
    vy
    @1
    c0
    wceq
    @2
    @10
    cU
    @1
    c0
    cr1
    fveq2
    eleq1d
    @1
    @3
    wceq
    @2
    @11
    cU
    @1
    @3
    cr1
    fveq2
    eleq1d
    @1
    @13
    wceq
    @2
    @14
    cU
    @1
    @13
    cr1
    fveq2
    eleq1d
    wph
    @10
    c0
    cU
    r10
    wph
    cU
    wun0.1
    wun0
    syl5eqel
    @3
    com
    wcel
    #
    wph
    @12
    @15
    wph
    @12
    wa
    #
    @15
    @16
    @11
    cpw
    #
    cU
    wcel
    @17
    @11
    cU
    wph
    cU
    cwun
    wcel
    @12
    wun0.1
    adantr
    wph
    @12
    simpr
    wunpw
    @16
    @14
    @18
    cU
    @16
    @3
    con0
    wcel
    @14
    @18
    wceq
    @3
    nnon
    @3
    r1suc
    syl
    eleq1d
    syl5ibr
    expd
    finds2
    @4
    @9
    @6
    wph
    @2
    @3
    cU
    eleq1
    imbi2d
    syl5ibcom
    rexlimiv
    cr1
    wfun
    #
    @7
    @5
    cr1
    con0
    wfn
    @19
    r1fnon
    con0
    cr1
    fnfun
    ax-mp
    vx
    @3
    com
    cr1
    fvelima
    mpan
    syl11
    ssrdv
end
