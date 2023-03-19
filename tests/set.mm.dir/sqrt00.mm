include "csqrt.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "sqrt0.mm"
include "eqeq2i.mm"
include "wb.mm"
include "0re.mm"
include "0le0.mm"
include "sqrt11.mm"
include "mpanr12.mm"
include "syl5bbr.mm"

theorem sqrt00
  let cA: class A


  assert |- ( ( A e. RR /\ 0 <_ A ) -> ( ( sqrt ` A ) = 0 <-> A = 0 ) )

  proof
    cA
    csqrt
    cfv
    #
    cc0
    wceq
    @0
    cc0
    csqrt
    cfv
    #
    wceq
    #
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    cA
    cc0
    wceq
    #
    @1
    cc0
    @0
    sqrt0
    eqeq2i
    @3
    cc0
    cr
    wcel
    cc0
    cc0
    cle
    wbr
    @2
    @4
    wb
    0re
    0le0
    cA
    cc0
    sqrt11
    mpanr12
    syl5bbr
end
