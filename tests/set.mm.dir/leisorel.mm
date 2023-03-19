include "clt.mm"
include "wiso.mm"
include "cxr.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wi.mm"
include "leiso.mm"
include "biimpcd.mm"
include "isorel.mm"
include "ex.mm"
include "syl6.mm"
include "3imp.mm"

theorem leisorel
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F Isom < , < ( A , B ) /\ ( A C_ RR* /\ B C_ RR* ) /\ ( C e. A /\ D e. A ) ) -> ( C <_ D <-> ( F ` C ) <_ ( F ` D ) ) )

  proof
    cA
    cB
    clt
    clt
    cF
    wiso
    #
    cA
    cxr
    wss
    cB
    cxr
    wss
    wa
    #
    cC
    cA
    wcel
    cD
    cA
    wcel
    wa
    #
    cC
    cD
    cle
    wbr
    cC
    cF
    cfv
    cD
    cF
    cfv
    cle
    wbr
    wb
    #
    @0
    @1
    cA
    cB
    cle
    cle
    cF
    wiso
    #
    @2
    @3
    wi
    @1
    @0
    @4
    cA
    cB
    cF
    leiso
    biimpcd
    @4
    @2
    @3
    cA
    cB
    cC
    cD
    cle
    cle
    cF
    isorel
    ex
    syl6
    3imp
end
