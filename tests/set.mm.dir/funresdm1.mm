include "wrel.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "cres.mm"
include "resundir.mm"
include "resdm.mm"
include "adantr.mm"
include "dmres.mm"
include "simpr.mm"
include "syl5eq.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"

theorem funresdm1
  let cA: class A
  let cB: class B


  assert |- ( ( Rel A /\ ( dom A i^i dom B ) = (/) ) -> ( ( A u. B ) |` dom A ) = A )

  proof
    cA
    wrel
    #
    cA
    cdm
    #
    cB
    cdm
    cin
    #
    c0
    wceq
    #
    wa
    #
    cA
    cB
    cun
    @1
    cres
    cA
    @1
    cres
    #
    cB
    @1
    cres
    #
    cun
    #
    cA
    cA
    cB
    @1
    resundir
    @4
    @7
    cA
    c0
    cun
    cA
    @4
    @5
    cA
    @6
    c0
    @0
    @5
    cA
    wceq
    @3
    cA
    resdm
    adantr
    @4
    @6
    cdm
    #
    c0
    wceq
    #
    @6
    c0
    wceq
    #
    @4
    @8
    @2
    c0
    cB
    @1
    dmres
    @0
    @3
    simpr
    syl5eq
    @6
    wrel
    @10
    @9
    wb
    cB
    @1
    relres
    @6
    reldm0
    ax-mp
    sylibr
    uneq12d
    cA
    un0
    syl6eq
    syl5eq
end
