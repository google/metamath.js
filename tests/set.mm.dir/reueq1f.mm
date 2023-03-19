include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "nfeq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "eubid.mm"
include "df-reu.mm"
include "3bitr4g.mm"

theorem reueq1f
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1f.1: |- F/_ x A
  assume raleq1f.2: |- F/_ x B


  assert |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) )

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
    weu
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    weu
    wph
    vx
    cA
    wreu
    wph
    vx
    cB
    wreu
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
    eubid
    wph
    vx
    cA
    df-reu
    wph
    vx
    cB
    df-reu
    3bitr4g
end
