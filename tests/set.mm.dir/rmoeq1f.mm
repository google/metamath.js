include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wrmo.mm"
include "nfeq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "mobid.mm"
include "df-rmo.mm"
include "3bitr4g.mm"

theorem rmoeq1f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1f.1: |- F/_ x A
  assume raleq1f.2: |- F/_ x B


  assert |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) )

  proof
    cA
    cB
    wceq
    #
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
    wmo
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    wph
    vx
    cA
    wrmo
    wph
    vx
    cB
    wrmo
    @0
    @3
    @5
    vx
    vx
    cA
    cB
    raleq1f.1
    raleq1f.2
    nfeq
    @0
    @2
    @4
    wph
    cA
    cB
    @1
    eleq2
    anbi1d
    mobid
    wph
    vx
    cA
    df-rmo
    wph
    vx
    cB
    df-rmo
    3bitr4g
end
