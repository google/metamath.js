include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "wa.mm"
include "wb.mm"
include "ralbiim.mm"
include "ceqsralv.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "reu6i.mm"
include "ex.mm"
include "sylbird.mm"
include "3impib.mm"
include "3com23.mm"

theorem eqreu
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume eqreu.1: |- ( x = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( ( B e. A /\ ps /\ A. x e. A ( ph -> x = B ) ) -> E! x e. A ph )

  proof
    cB
    cA
    wcel
    #
    wph
    vx
    cv
    cB
    wceq
    #
    wi
    vx
    cA
    wral
    #
    wps
    wph
    vx
    cA
    wreu
    #
    @0
    @2
    wps
    @3
    @0
    @2
    wps
    wa
    #
    wph
    @1
    wb
    vx
    cA
    wral
    #
    @3
    @5
    @2
    @1
    wph
    wi
    vx
    cA
    wral
    #
    wa
    @0
    @4
    wph
    @1
    vx
    cA
    ralbiim
    @0
    @6
    wps
    @2
    wph
    wps
    vx
    cB
    cA
    eqreu.1
    ceqsralv
    anbi2d
    syl5bb
    @0
    @5
    @3
    wph
    vx
    cA
    cB
    reu6i
    ex
    sylbird
    3impib
    3com23
end
