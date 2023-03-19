include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "copab.mm"
include "cxp.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "brel.mm"
include "cop.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "opelopab2a.mm"
include "syl5bb.mm"
include "biadan2.mm"

theorem brab2a
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume brab2a.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
  assume brab2a.2: |- R = { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ps x
  disjoint ps y
  assert |- ( A R B <-> ( ( A e. C /\ B e. D ) /\ ps ) )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    wps
    cA
    cB
    cC
    cD
    cR
    cR
    vx
    cv
    cC
    wcel
    vy
    cv
    cD
    wcel
    wa
    wph
    wa
    vx
    vy
    copab
    #
    cC
    cD
    cxp
    brab2a.2
    wph
    vx
    vy
    cC
    cD
    opabssxp
    eqsstri
    brel
    @0
    cA
    cB
    cop
    #
    @2
    wcel
    #
    @1
    wps
    @0
    @3
    cR
    wcel
    @4
    cA
    cB
    cR
    df-br
    cR
    @2
    @3
    brab2a.2
    eleq2i
    bitri
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    brab2a.1
    opelopab2a
    syl5bb
    biadan2
end
