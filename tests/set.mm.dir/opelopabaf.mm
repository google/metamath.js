include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wsbc.mm"
include "opelopabsb.mm"
include "cvv.mm"
include "wb.mm"
include "nfv.mm"
include "sbc2iegf.mm"
include "mp2an.mm"
include "bitri.mm"

theorem opelopabaf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume opelopabaf.x: |- F/ x ps
  assume opelopabaf.y: |- F/ y ps
  assume opelopabaf.1: |- A e. _V
  assume opelopabaf.2: |- B e. _V
  assume opelopabaf.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps )

  proof
    cA
    cB
    cop
    wph
    vx
    vy
    copab
    wcel
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    #
    wps
    wph
    vx
    vy
    cA
    cB
    opelopabsb
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    #
    @0
    wps
    wb
    opelopabaf.1
    opelopabaf.2
    wph
    wps
    vx
    vy
    cA
    cB
    cvv
    cvv
    opelopabaf.x
    opelopabaf.y
    @1
    vx
    nfv
    opelopabaf.3
    sbc2iegf
    mp2an
    bitri
end
