include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "impl.mm"
include "sbcied.mm"

theorem sbc2iedv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume sbc2iedv.1: |- A e. _V
  assume sbc2iedv.2: |- B e. _V
  assume sbc2iedv.3: |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint ch x
  disjoint ch y
  assert |- ( ph -> ( [. A / x ]. [. B / y ]. ps <-> ch ) )

  proof
    wph
    wps
    vy
    cB
    wsbc
    wch
    vx
    cA
    cvv
    cA
    cvv
    wcel
    wph
    sbc2iedv.1
    a1i
    wph
    vx
    cv
    cA
    wceq
    #
    wa
    #
    wps
    wch
    vy
    cB
    cvv
    cB
    cvv
    wcel
    @1
    sbc2iedv.2
    a1i
    wph
    @0
    vy
    cv
    cB
    wceq
    wps
    wch
    wb
    sbc2iedv.3
    impl
    sbcied
    sbcied
end
