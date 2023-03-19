include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "wex.mm"
include "df-rex.mm"
include "an12.mm"
include "exbii.mm"
include "bitr4i.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "ceqsexgv.mm"
include "bianabs.mm"
include "syl5bb.mm"

theorem ceqsrexv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ceqsrexv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( A e. B -> ( E. x e. B ( x = A /\ ph ) <-> ps ) )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wa
    #
    vx
    cB
    wrex
    #
    @1
    @0
    cB
    wcel
    #
    wph
    wa
    #
    wa
    #
    vx
    wex
    #
    cA
    cB
    wcel
    #
    wps
    @3
    @4
    @2
    wa
    #
    vx
    wex
    @7
    @2
    vx
    cB
    df-rex
    @6
    @9
    vx
    @1
    @4
    wph
    an12
    exbii
    bitr4i
    @8
    @7
    wps
    @5
    @8
    wps
    wa
    vx
    cA
    cB
    @1
    @4
    @8
    wph
    wps
    @0
    cA
    cB
    eleq1
    ceqsrexv.1
    anbi12d
    ceqsexgv
    bianabs
    syl5bb
end
