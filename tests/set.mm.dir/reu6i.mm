include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "reu6.mm"
include "sylibr.mm"

theorem reu6i
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let wps: wff ps

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  disjoint ps x
  assert |- ( ( B e. A /\ A. x e. A ( ph <-> x = B ) ) -> E! x e. A ph )

  proof
    cB
    cA
    wcel
    wph
    vx
    cv
    #
    cB
    wceq
    #
    wb
    #
    vx
    cA
    wral
    #
    wa
    wph
    @0
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    cA
    wral
    #
    vy
    cA
    wrex
    wph
    vx
    cA
    wreu
    @7
    @3
    vy
    cB
    cA
    @4
    cB
    wceq
    #
    @6
    @2
    vx
    cA
    @8
    @5
    @1
    wph
    @4
    cB
    @0
    eqeq2
    bibi2d
    ralbidv
    rspcev
    wph
    vx
    vy
    cA
    reu6
    sylibr
end
