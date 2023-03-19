include "crab.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-rab.mm"
include "sseq12i.mm"
include "ss2ab.mm"
include "df-ral.mm"
include "imdistan.mm"
include "albii.mm"
include "bitr2i.mm"
include "3bitri.mm"

theorem ss2rab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( { x e. A | ph } C_ { x e. A | ps } <-> A. x e. A ( ph -> ps ) )

  proof
    wph
    vx
    cA
    crab
    #
    wps
    vx
    cA
    crab
    #
    wss
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    @2
    wps
    wa
    #
    vx
    cab
    #
    wss
    @3
    @5
    wi
    #
    vx
    wal
    #
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    @0
    @4
    @1
    @6
    wph
    vx
    cA
    df-rab
    wps
    vx
    cA
    df-rab
    sseq12i
    @3
    @5
    vx
    ss2ab
    @10
    @2
    @9
    wi
    #
    vx
    wal
    @8
    @9
    vx
    cA
    df-ral
    @11
    @7
    vx
    @2
    wph
    wps
    imdistan
    albii
    bitr2i
    3bitri
end
