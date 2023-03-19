include "cv.mm"
include "wceq.mm"
include "sylan9bb.mm"
include "brabga.mm"

theorem brabg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume opelopabg.1: |- ( x = A -> ( ph <-> ps ) )
  assume opelopabg.2: |- ( y = B -> ( ps <-> ch ) )
  assume brabg.5: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ( A R B <-> ch ) )

  proof
    wph
    wch
    vx
    vy
    cA
    cB
    cR
    cC
    cD
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    cv
    cB
    wceq
    wch
    opelopabg.1
    opelopabg.2
    sylan9bb
    brabg.5
    brabga
end
