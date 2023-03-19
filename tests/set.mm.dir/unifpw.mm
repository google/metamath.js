include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "inss1.mm"
include "unissi.mm"
include "unipw.mm"
include "sseqtri.mm"
include "sseli.mm"
include "csn.mm"
include "wss.mm"
include "snelpwi.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "elssuni.mm"
include "syl.mm"
include "snidg.mm"
include "sseldd.mm"
include "impbii.mm"
include "eqriv.mm"

theorem unifpw
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cF: class F


  assert |- U. ( ~P A i^i Fin ) = A

  proof
    va
    cA
    cpw
    #
    cfn
    cin
    #
    cuni
    #
    cA
    va
    cv
    #
    @2
    wcel
    @3
    cA
    wcel
    #
    @2
    cA
    @3
    @2
    @0
    cuni
    cA
    @1
    @0
    @0
    cfn
    inss1
    unissi
    cA
    unipw
    sseqtri
    sseli
    @4
    @3
    csn
    #
    @2
    @3
    @4
    @5
    @1
    wcel
    @5
    @2
    wss
    @4
    @0
    cfn
    @5
    @3
    cA
    snelpwi
    @5
    cfn
    wcel
    @4
    @3
    snfi
    a1i
    elind
    @5
    @1
    elssuni
    syl
    @3
    cA
    snidg
    sseldd
    impbii
    eqriv
end
