include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "copab.mm"
include "wsbc.mm"
include "df-br.mm"
include "eleq2i.mm"
include "opelopabsb.mm"
include "3bitri.mm"

theorem brabsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vz: setvar z
  let vw: setvar w
  assume brabsb.1: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint B x
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint ph w
  disjoint ph z
  assert |- ( A R B <-> [. A / x ]. [. B / y ]. ph )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cop
    #
    cR
    wcel
    @0
    wph
    vx
    vy
    copab
    #
    wcel
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    cA
    cB
    cR
    df-br
    cR
    @1
    @0
    brabsb.1
    eleq2i
    wph
    vx
    vy
    cA
    cB
    opelopabsb
    3bitri
end
