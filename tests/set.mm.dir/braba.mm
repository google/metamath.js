include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "wb.mm"
include "brabga.mm"
include "mp2an.mm"

theorem braba
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  assume opelopaba.1: |- A e. _V
  assume opelopaba.2: |- B e. _V
  assume opelopaba.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
  assume braba.4: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( A R B <-> ps )

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
    cR
    cvv
    cvv
    opelopaba.3
    braba.4
    brabga
    mp2an
end
