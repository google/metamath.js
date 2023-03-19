include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "csup.mm"
include "wbr.mm"
include "cif.mm"
include "cpr.mm"
include "dfsn2.mm"
include "supeq1i.mm"
include "wceq.mm"
include "suppr.mm"
include "3anidm23.mm"
include "syl5eq.mm"
include "ifid.mm"
include "syl6eq.mm"

theorem supsn
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y
  let cC: class C


  assert |- ( ( R Or A /\ B e. A ) -> sup ( { B } , A , R ) = B )

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
    csup
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
    csup
    #
    @6
    cA
    @3
    @7
    cR
    cB
    dfsn2
    supeq1i
    @0
    @1
    @8
    @6
    wceq
    cA
    cB
    cB
    cR
    suppr
    3anidm23
    syl5eq
    @5
    cB
    ifid
    syl6eq
end
