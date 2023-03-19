include "cdir.mm"
include "wcel.mm"
include "w3a.mm"
include "ctail.mm"
include "cfv.mm"
include "csn.mm"
include "cima.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "tailval.mm"
include "eleq2d.mm"
include "3adant3.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem eltail
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let vd: setvar d
  let vx: setvar x
  assume tailfval.1: |- X = dom D


  assert |- ( ( D e. DirRel /\ A e. X /\ B e. C ) -> ( B e. ( ( tail ` D ) ` A ) <-> A D B ) )

  proof
    cD
    cdir
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cC
    wcel
    #
    w3a
    cB
    cA
    cD
    ctail
    cfv
    cfv
    #
    wcel
    #
    cB
    cD
    cA
    csn
    cima
    #
    wcel
    #
    cA
    cB
    cD
    wbr
    #
    @0
    @1
    @4
    @6
    wb
    @2
    @0
    @1
    wa
    @3
    @5
    cB
    cA
    cD
    cX
    tailfval.1
    tailval
    eleq2d
    3adant3
    @1
    @2
    @6
    @7
    wb
    @0
    @1
    @2
    wa
    @6
    cA
    cB
    cop
    cD
    wcel
    @7
    cD
    cA
    cB
    cX
    cC
    elimasng
    cA
    cB
    cD
    df-br
    syl6bbr
    3adant1
    bitrd
end
