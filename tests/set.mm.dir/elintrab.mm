include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "wi.mm"
include "wal.mm"
include "crab.mm"
include "wral.mm"
include "elintab.mm"
include "impexp.mm"
include "albii.mm"
include "bitri.mm"
include "df-rab.mm"
include "inteqi.mm"
include "eleq2i.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem elintrab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume inteqab.1: |- A e. _V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph y
  assert |- ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) )

  proof
    cA
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    vx
    cab
    #
    cint
    #
    wcel
    #
    @1
    wph
    cA
    @0
    wcel
    #
    wi
    #
    wi
    #
    vx
    wal
    #
    cA
    wph
    vx
    cB
    crab
    #
    cint
    #
    wcel
    @7
    vx
    cB
    wral
    @5
    @2
    @6
    wi
    #
    vx
    wal
    @9
    @2
    vx
    cA
    inteqab.1
    elintab
    @12
    @8
    vx
    @1
    wph
    @6
    impexp
    albii
    bitri
    @11
    @4
    cA
    @10
    @3
    wph
    vx
    cB
    df-rab
    inteqi
    eleq2i
    @7
    vx
    cB
    df-ral
    3bitr4i
end
