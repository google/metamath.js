include "com.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cr1.mm"
include "cfv.mm"
include "cwun.mm"
include "adantr.mm"
include "cima.mm"
include "wss.mm"
include "wral.mm"
include "wunr1om.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "wlim.mm"
include "r1funlim.mm"
include "simpli.mm"
include "simpri.mm"
include "limomss.mm"
include "ax-mp.mm"
include "funimass4.mm"
include "mp2an.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "simpr.mm"
include "sseldi.mm"
include "onssr1.mm"
include "syl.mm"
include "wunss.mm"
include "ex.mm"
include "ssrdv.mm"

theorem wunom
  let wph: wff ph
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume wun0.1: |- ( ph -> U e. WUni )


  assert |- ( ph -> _om C_ U )

  proof
    wph
    vx
    com
    cU
    wph
    vx
    cv
    #
    com
    wcel
    #
    @0
    cU
    wcel
    wph
    @1
    wa
    #
    @0
    cr1
    cfv
    #
    @0
    cU
    wph
    cU
    cwun
    wcel
    @1
    wun0.1
    adantr
    wph
    @3
    cU
    wcel
    #
    vx
    com
    wph
    cr1
    com
    cima
    cU
    wss
    #
    @4
    vx
    com
    wral
    #
    wph
    cU
    wun0.1
    wunr1om
    cr1
    wfun
    #
    com
    cr1
    cdm
    #
    wss
    #
    @5
    @6
    wb
    @7
    @8
    wlim
    #
    r1funlim
    simpli
    @10
    @9
    @7
    @10
    r1funlim
    simpri
    @8
    limomss
    ax-mp
    #
    vx
    com
    cU
    cr1
    funimass4
    mp2an
    sylib
    r19.21bi
    @2
    @0
    @8
    wcel
    @0
    @3
    wss
    @2
    com
    @8
    @0
    @11
    wph
    @1
    simpr
    sseldi
    @0
    onssr1
    syl
    wunss
    ex
    ssrdv
end
