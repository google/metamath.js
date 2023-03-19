include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "csle.mm"
include "slttrieq2.mm"
include "slenlt.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "bitr4d.mm"

theorem sletri3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. No /\ B e. No ) -> ( A = B <-> ( A <_s B /\ B <_s A ) ) )

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
    wceq
    cA
    cB
    cslt
    wbr
    wn
    #
    cB
    cA
    cslt
    wbr
    wn
    #
    wa
    #
    cA
    cB
    csle
    wbr
    #
    cB
    cA
    csle
    wbr
    #
    wa
    #
    cA
    cB
    slttrieq2
    @2
    @8
    @4
    @3
    wa
    @5
    @2
    @6
    @4
    @7
    @3
    cA
    cB
    slenlt
    @1
    @0
    @7
    @3
    wb
    cB
    cA
    slenlt
    ancoms
    anbi12d
    @4
    @3
    ancom
    syl6bb
    bitr4d
end
