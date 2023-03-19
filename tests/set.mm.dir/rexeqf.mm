include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "nfeq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "exbid.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem rexeqf
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  param cB: class B
  assume raleq1f.1: |- F/_ x A
  assume raleq1f.2: |- F/_ x B


  assert |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) )

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
    wex
    @1
    cB
    wcel
    #
    wph
    wa
    #
    vx
    wex
    wph
    vx
    cA
    wrex
    wph
    vx
    cB
    wrex
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
    exbid
    wph
    vx
    cA
    df-rex
    wph
    vx
    cB
    df-rex
    3bitr4g
end
