include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cwun.mm"
include "wtr.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "iswun.mm"
include "ibi.mm"
include "simp2d.mm"
include "syl.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "wss.mm"
include "0ss.mm"
include "a1i.mm"
include "wunss.mm"
include "exlimddv.mm"

theorem wun0
  let wph: wff ph
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume wun0.1: |- ( ph -> U e. WUni )


  assert |- ( ph -> (/) e. U )

  proof
    wph
    vx
    cv
    #
    cU
    wcel
    #
    c0
    cU
    wcel
    vx
    wph
    cU
    c0
    wne
    #
    @1
    vx
    wex
    wph
    cU
    cwun
    wcel
    #
    @2
    wun0.1
    @3
    cU
    wtr
    #
    @2
    @0
    cuni
    cU
    wcel
    @0
    cpw
    cU
    wcel
    @0
    vy
    cv
    cpr
    cU
    wcel
    vy
    cU
    wral
    w3a
    vx
    cU
    wral
    #
    @3
    @4
    @2
    @5
    w3a
    vx
    vy
    cU
    cwun
    iswun
    ibi
    simp2d
    syl
    vx
    cU
    n0
    sylib
    wph
    @1
    wa
    #
    @0
    c0
    cU
    wph
    @3
    @1
    wun0.1
    adantr
    wph
    @1
    simpr
    c0
    @0
    wss
    @6
    @0
    0ss
    a1i
    wunss
    exlimddv
end
