include "wcel.mm"
include "cuni.mm"
include "cfi.mm"
include "cfv.mm"
include "ssfii.mm"
include "unissd.mm"
include "wss.mm"
include "cpw.mm"
include "fipwuni.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "a1i.mm"
include "eqssd.mm"

theorem fiuni
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> U. A = U. ( fi ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cuni
    #
    cA
    cfi
    cfv
    #
    cuni
    #
    @0
    cA
    @2
    cA
    cV
    ssfii
    unissd
    @3
    @1
    wss
    @0
    @3
    @1
    cpw
    #
    cuni
    @1
    @2
    @4
    cA
    fipwuni
    unissi
    @1
    unipw
    sseqtri
    a1i
    eqssd
end
