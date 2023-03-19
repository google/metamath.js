include "cv.mm"
include "wceq.mm"
include "sylan9bb.mm"
include "opelopabga.mm"

theorem opelopabg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume opelopabg.1: |- ( x = A -> ( ph <-> ps ) )
  assume opelopabg.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) )

  proof
    wph
    wch
    vx
    vy
    cA
    cB
    cV
    cW
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
    opelopabga
end
