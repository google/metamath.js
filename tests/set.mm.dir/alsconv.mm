include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "walsc.mm"
include "walsi.mm"
include "df-ral.mm"
include "anbi1i.mm"
include "df-alsc.mm"
include "df-alsi.mm"
include "3bitr4ri.mm"

theorem alsconv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k


  assert |- ( A! x ( x e. A -> ph ) <-> A! x e. A ph )

  proof
    wph
    vx
    cA
    wral
    #
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    #
    wa
    @1
    wph
    wi
    vx
    wal
    #
    @2
    wa
    wph
    vx
    cA
    walsc
    @1
    wph
    vx
    walsi
    @0
    @3
    @2
    wph
    vx
    cA
    df-ral
    anbi1i
    wph
    vx
    cA
    df-alsc
    @1
    wph
    vx
    df-alsi
    3bitr4ri
end
