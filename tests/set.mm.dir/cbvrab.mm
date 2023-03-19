include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "wsb.mm"
include "nfv.mm"
include "nfcri.mm"
include "nfs1v.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "cbvab.mm"
include "nfsb.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "eqtri.mm"
include "df-rab.mm"
include "3eqtr4i.mm"

theorem cbvrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvrab.1: |- F/_ x A
  assume cbvrab.2: |- F/_ y A
  assume cbvrab.3: |- F/ y ph
  assume cbvrab.4: |- F/ x ps
  assume cbvrab.5: |- ( x = y -> ( ph <-> ps ) )


  assert |- { x e. A | ph } = { y e. A | ps }

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    vy
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vy
    cab
    #
    wph
    vx
    cA
    crab
    wps
    vy
    cA
    crab
    @3
    vz
    cv
    #
    cA
    wcel
    #
    wph
    vx
    vz
    wsb
    #
    wa
    #
    vz
    cab
    @7
    @2
    @11
    vx
    vz
    @2
    vz
    nfv
    @9
    @10
    vx
    vx
    vz
    cA
    cbvrab.1
    nfcri
    wph
    vx
    vz
    nfs1v
    nfan
    vx
    vz
    weq
    @1
    @9
    wph
    @10
    @0
    @8
    cA
    eleq1
    wph
    vx
    vz
    sbequ12
    anbi12d
    cbvab
    @11
    @6
    vz
    vy
    @9
    @10
    vy
    vy
    vz
    cA
    cbvrab.2
    nfcri
    wph
    vx
    vz
    vy
    cbvrab.3
    nfsb
    nfan
    @6
    vz
    nfv
    vz
    vy
    weq
    #
    @9
    @5
    @10
    wps
    @8
    @4
    cA
    eleq1
    @12
    @10
    wph
    vx
    vy
    wsb
    wps
    wph
    vz
    vy
    vx
    sbequ
    wph
    wps
    vx
    vy
    cbvrab.4
    cbvrab.5
    sbie
    syl6bb
    anbi12d
    cbvab
    eqtri
    wph
    vx
    cA
    df-rab
    wps
    vy
    cA
    df-rab
    3eqtr4i
end
