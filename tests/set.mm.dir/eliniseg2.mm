include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "elrelimasn.mm"
include "ax-mp.mm"
include "relbrcnvg.mm"
include "syl5bb.mm"

theorem eliniseg2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( Rel A -> ( C e. ( `' A " { B } ) <-> C A B ) )

  proof
    cC
    cA
    ccnv
    #
    cB
    csn
    cima
    wcel
    #
    cB
    cC
    @0
    wbr
    #
    cA
    wrel
    cC
    cB
    cA
    wbr
    @0
    wrel
    @1
    @2
    wb
    cA
    relcnv
    cB
    cC
    @0
    elrelimasn
    ax-mp
    cB
    cC
    cA
    relbrcnvg
    syl5bb
end
