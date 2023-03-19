include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "breq2.mm"
include "cvv.mm"
include "cab.mm"
include "wceq.mm"
include "imasng.mm"
include "ax-mp.mm"
include "elab2.mm"
include "df-br.mm"
include "bitri.mm"

theorem elimasn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume elimasn.1: |- B e. _V
  assume elimasn.2: |- C e. _V


  assert |- ( C e. ( A " { B } ) <-> <. B , C >. e. A )

  proof
    cC
    cA
    cB
    csn
    cima
    #
    wcel
    cB
    cC
    cA
    wbr
    #
    cB
    cC
    cop
    cA
    wcel
    cB
    vx
    cv
    #
    cA
    wbr
    #
    @1
    vx
    cC
    @0
    elimasn.2
    @2
    cC
    cB
    cA
    breq2
    cB
    cvv
    wcel
    @0
    @3
    vx
    cab
    wceq
    elimasn.1
    vx
    cB
    cvv
    cA
    imasng
    ax-mp
    elab2
    cB
    cC
    cA
    df-br
    bitri
end
