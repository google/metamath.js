include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "wb.mm"
include "brabg.mm"
include "mp2an.mm"

theorem brab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume opelopab.1: |- A e. _V
  assume opelopab.2: |- B e. _V
  assume opelopab.3: |- ( x = A -> ( ph <-> ps ) )
  assume opelopab.4: |- ( y = B -> ( ps <-> ch ) )
  assume brab.5: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( A R B <-> ch )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cR
    wbr
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
    cR
    opelopab.3
    opelopab.4
    brab.5
    brabg
    mp2an
end
