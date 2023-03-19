include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "copab.mm"
include "wb.mm"
include "opelopabg.mm"
include "mp2an.mm"

theorem opelopab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume opelopab.1: |- A e. _V
  assume opelopab.2: |- B e. _V
  assume opelopab.3: |- ( x = A -> ( ph <-> ps ) )
  assume opelopab.4: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch )

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
    wch
    wb
    opelopab.1
    opelopab.2
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cvv
    cvv
    opelopab.3
    opelopab.4
    opelopabg
    mp2an
end
