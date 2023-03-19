include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cinf.mm"
include "wbr.mm"
include "cif.mm"
include "cpr.mm"
include "dfsn2.mm"
include "infeq1i.mm"
include "wceq.mm"
include "infpr.mm"
include "3anidm23.mm"
include "syl5eq.mm"
include "ifid.mm"
include "syl6eq.mm"

theorem infsn
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( R Or A /\ B e. A ) -> inf ( { B } , A , R ) = B )

  proof
    cA
    cR
    wor
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    csn
    #
    cA
    cR
    cinf
    #
    cB
    cB
    cR
    wbr
    #
    cB
    cB
    cif
    #
    cB
    @2
    @4
    cB
    cB
    cpr
    #
    cA
    cR
    cinf
    #
    @6
    cA
    @3
    @7
    cR
    cB
    dfsn2
    infeq1i
    @0
    @1
    @8
    @6
    wceq
    cA
    cB
    cB
    cR
    infpr
    3anidm23
    syl5eq
    @5
    cB
    ifid
    syl6eq
end
