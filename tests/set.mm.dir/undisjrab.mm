include "wa.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wxo.mm"
include "cin.mm"
include "cun.mm"
include "wn.mm"
include "wral.mm"
include "wb.mm"
include "rabeq0.mm"
include "wnan.mm"
include "df-nan.mm"
include "nanorxor.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "rabbi.mm"
include "3bitri.mm"
include "inrab.mm"
include "eqeq1i.mm"
include "unrab.mm"
include "3bitr4i.mm"

theorem undisjrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( ( { x e. A | ph } i^i { x e. A | ps } ) = (/) <-> ( { x e. A | ph } u. { x e. A | ps } ) = { x e. A | ( ph \/_ ps ) } )

  proof
    wph
    wps
    wa
    #
    vx
    cA
    crab
    #
    c0
    wceq
    #
    wph
    wps
    wo
    #
    vx
    cA
    crab
    #
    wph
    wps
    wxo
    #
    vx
    cA
    crab
    #
    wceq
    #
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
    cin
    #
    c0
    wceq
    @8
    @9
    cun
    #
    @6
    wceq
    @2
    @0
    wn
    #
    vx
    cA
    wral
    @3
    @5
    wb
    #
    vx
    cA
    wral
    @7
    @0
    vx
    cA
    rabeq0
    @12
    @13
    vx
    cA
    @12
    wph
    wps
    wnan
    @13
    wph
    wps
    df-nan
    wph
    wps
    nanorxor
    bitr3i
    ralbii
    @3
    @5
    vx
    cA
    rabbi
    3bitri
    @10
    @1
    c0
    wph
    wps
    vx
    cA
    inrab
    eqeq1i
    @11
    @4
    @6
    wph
    wps
    vx
    cA
    unrab
    eqeq1i
    3bitr4i
end
