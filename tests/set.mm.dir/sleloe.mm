include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "csle.mm"
include "wbr.mm"
include "cslt.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "slenlt.mm"
include "orcom.mm"
include "eqcom.mm"
include "orbi1i.mm"
include "bitri.mm"
include "wb.mm"
include "wor.mm"
include "sltso.mm"
include "sotric.mm"
include "mpan.mm"
include "ancoms.mm"
include "con2bid.mm"
include "syl5bb.mm"
include "bitr4d.mm"

theorem sleloe
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A <_s B <-> ( A <s B \/ A = B ) ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    wa
    #
    cA
    cB
    csle
    wbr
    cB
    cA
    cslt
    wbr
    #
    wn
    #
    cA
    cB
    cslt
    wbr
    #
    cA
    cB
    wceq
    #
    wo
    #
    cA
    cB
    slenlt
    @7
    cB
    cA
    wceq
    #
    @5
    wo
    #
    @2
    @4
    @7
    @6
    @5
    wo
    @9
    @5
    @6
    orcom
    @6
    @8
    @5
    cA
    cB
    eqcom
    orbi1i
    bitri
    @2
    @3
    @9
    @1
    @0
    @3
    @9
    wn
    wb
    #
    csur
    cslt
    wor
    @1
    @0
    wa
    @10
    sltso
    csur
    cB
    cA
    cslt
    sotric
    mpan
    ancoms
    con2bid
    syl5bb
    bitr4d
end
