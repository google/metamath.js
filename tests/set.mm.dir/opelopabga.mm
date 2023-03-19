include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "copsex2g.mm"
include "syl5bb.mm"

theorem opelopabga
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume opelopabga.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) )

  proof
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    wcel
    @0
    vx
    cv
    vy
    cv
    cop
    wceq
    wph
    wa
    vy
    wex
    vx
    wex
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    wps
    wph
    vx
    vy
    @0
    elopab
    wph
    wps
    vx
    vy
    cA
    cB
    cV
    cW
    opelopabga.1
    copsex2g
    syl5bb
end
