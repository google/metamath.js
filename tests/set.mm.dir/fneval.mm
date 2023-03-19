include "wbr.mm"
include "cfne.mm"
include "wa.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "ccnv.mm"
include "cin.mm"
include "breqi.mm"
include "brin.mm"
include "fnerel.mm"
include "relbrcnv.mm"
include "anbi2i.mm"
include "bitri.mm"
include "cuni.mm"
include "wss.mm"
include "eqid.mm"
include "isfne4b.mm"
include "eqcom.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "bi2anan9r.mm"
include "eqss.mm"
include "anandi.mm"
include "syl6bbr.mm"
include "unieq.mm"
include "unitg.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "syl5bb.mm"

theorem fneval
  let cA: class A
  let cB: class B
  let c.sm: class .~
  let cV: class V
  let cW: class W
  assume fneval.1: |- .~ = ( Fne i^i `' Fne )


  assert |- ( ( A e. V /\ B e. W ) -> ( A .~ B <-> ( topGen ` A ) = ( topGen ` B ) ) )

  proof
    cA
    cB
    c.sm
    wbr
    #
    cA
    cB
    cfne
    wbr
    #
    cB
    cA
    cfne
    wbr
    #
    wa
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    ctg
    cfv
    #
    cB
    ctg
    cfv
    #
    wceq
    #
    @0
    cA
    cB
    cfne
    cfne
    ccnv
    #
    cin
    #
    wbr
    #
    @3
    cA
    cB
    c.sm
    @11
    fneval.1
    breqi
    @12
    @1
    cA
    cB
    @10
    wbr
    #
    wa
    @3
    cA
    cB
    cfne
    @10
    brin
    @13
    @2
    @1
    cA
    cB
    cfne
    fnerel
    relbrcnv
    anbi2i
    bitri
    bitri
    @6
    @3
    cA
    cuni
    #
    cB
    cuni
    #
    wceq
    #
    @9
    wa
    #
    @9
    @6
    @3
    @16
    @7
    @8
    wss
    #
    wa
    #
    @16
    @8
    @7
    wss
    #
    wa
    #
    wa
    #
    @17
    @5
    @1
    @19
    @4
    @2
    @21
    cA
    cB
    cW
    @14
    @15
    @14
    eqid
    #
    @15
    eqid
    #
    isfne4b
    @4
    @2
    @15
    @14
    wceq
    #
    @20
    wa
    @21
    cB
    cA
    cV
    @15
    @14
    @24
    @23
    isfne4b
    @25
    @16
    @20
    @15
    @14
    eqcom
    anbi1i
    syl6bb
    bi2anan9r
    @17
    @16
    @18
    @20
    wa
    #
    wa
    @22
    @9
    @26
    @16
    @7
    @8
    eqss
    anbi2i
    @16
    @18
    @20
    anandi
    bitri
    syl6bbr
    @6
    @9
    @16
    @9
    @7
    cuni
    #
    @8
    cuni
    #
    wceq
    @6
    @16
    @7
    @8
    unieq
    @4
    @5
    @27
    @14
    @28
    @15
    cA
    cV
    unitg
    cB
    cW
    unitg
    eqeqan12d
    syl5ib
    pm4.71rd
    bitr4d
    syl5bb
end
