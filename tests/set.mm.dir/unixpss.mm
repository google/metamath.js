include "cxp.mm"
include "cuni.mm"
include "cun.mm"
include "cpw.mm"
include "xpsspw.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"

theorem unixpss
  let cA: class A
  let cB: class B


  assert |- U. U. ( A X. B ) C_ ( A u. B )

  proof
    cA
    cB
    cxp
    #
    cuni
    #
    cuni
    cA
    cB
    cun
    #
    cpw
    #
    cuni
    @2
    @1
    @3
    @1
    @3
    cpw
    #
    cuni
    @3
    @0
    @4
    cA
    cB
    xpsspw
    unissi
    @3
    unipw
    sseqtri
    unissi
    @2
    unipw
    sseqtri
end
