include "cfne.mm"
include "wbr.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "eqid.mm"
include "fnebas.mm"
include "sylan9eq.mm"
include "cvv.mm"
include "wcel.mm"
include "fnerel.mm"
include "brrelex2i.mm"
include "isfne4b.mm"
include "simplbda.mm"
include "mpancom.mm"
include "sylan9ss.mm"
include "wb.mm"
include "adantl.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem fnetr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A Fne B /\ B Fne C ) -> A Fne C )

  proof
    cA
    cB
    cfne
    wbr
    #
    cB
    cC
    cfne
    wbr
    #
    wa
    #
    cA
    cC
    cfne
    wbr
    #
    cA
    cuni
    #
    cC
    cuni
    #
    wceq
    #
    cA
    ctg
    cfv
    #
    cC
    ctg
    cfv
    #
    wss
    #
    @0
    @1
    @4
    cB
    cuni
    #
    @5
    cA
    cB
    @4
    @10
    @4
    eqid
    #
    @10
    eqid
    #
    fnebas
    cB
    cC
    @10
    @5
    @12
    @5
    eqid
    #
    fnebas
    sylan9eq
    @0
    @1
    @7
    cB
    ctg
    cfv
    #
    @8
    cB
    cvv
    wcel
    #
    @0
    @7
    @14
    wss
    #
    cA
    cB
    cfne
    fnerel
    brrelex2i
    @15
    @0
    @4
    @10
    wceq
    @16
    cA
    cB
    cvv
    @4
    @10
    @11
    @12
    isfne4b
    simplbda
    mpancom
    cC
    cvv
    wcel
    #
    @1
    @14
    @8
    wss
    #
    cB
    cC
    cfne
    fnerel
    brrelex2i
    #
    @17
    @1
    @10
    @5
    wceq
    @18
    cB
    cC
    cvv
    @10
    @5
    @12
    @13
    isfne4b
    simplbda
    mpancom
    sylan9ss
    @2
    @17
    @3
    @6
    @9
    wa
    wb
    @1
    @17
    @0
    @19
    adantl
    cA
    cC
    cvv
    @4
    @5
    @11
    @13
    isfne4b
    syl
    mpbir2and
end
