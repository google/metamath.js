include "wbr.mm"
include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "df-br.mm"
include "eleq2i.mm"
include "bitri.mm"
include "opelopabga.mm"
include "syl5bb.mm"

theorem brabga
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let cW: class W
  assume opelopabga.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
  assume brabga.2: |- R = { <. x , y >. | ph }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    #
    wcel
    #
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    wps
    @0
    @1
    cR
    wcel
    @3
    cA
    cB
    cR
    df-br
    cR
    @2
    @1
    brabga.2
    eleq2i
    bitri
    wph
    wps
    vx
    vy
    cA
    cB
    cV
    cW
    opelopabga.1
    opelopabga
    syl5bb
end
