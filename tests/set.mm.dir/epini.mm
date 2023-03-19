include "cep.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "epelc.mm"
include "bitri.mm"
include "eqriv.mm"

theorem epini
  let cA: class A
  let vx: setvar x
  assume epini.1: |- A e. _V


  assert |- ( `' _E " { A } ) = A

  proof
    vx
    cep
    ccnv
    cA
    csn
    cima
    #
    cA
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cA
    cep
    wbr
    #
    @1
    cA
    wcel
    cA
    cvv
    wcel
    @2
    @3
    wb
    epini.1
    cep
    cA
    @1
    cvv
    vx
    vex
    eliniseg
    ax-mp
    @1
    cA
    epini.1
    epelc
    bitri
    eqriv
end
