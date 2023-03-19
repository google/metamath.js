include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "copab.mm"
include "wb.mm"
include "opelopabga.mm"
include "mp2an.mm"

theorem opelopaba
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume opelopaba.1: |- A e. _V
  assume opelopaba.2: |- B e. _V
  assume opelopaba.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    wph
    vx
    vy
    copab
    wcel
    wps
    wb
    opelopaba.1
    opelopaba.2
    wph
    wps
    vx
    vy
    cA
    cB
    cvv
    cvv
    opelopaba.3
    opelopabga
    mp2an
end
