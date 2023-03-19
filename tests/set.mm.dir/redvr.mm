include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "crefld.mm"
include "cdvr.mm"
include "cfv.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cui.mm"
include "wceq.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "a1i.mm"
include "simp1.mm"
include "wa.mm"
include "3simpc.mm"
include "wb.mm"
include "simpri.mm"
include "rebase.mm"
include "eqid.mm"
include "re0g.mm"
include "drngunit.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "df-refld.mm"
include "cnflddiv.mm"
include "subrgdv.mm"
include "syl3anc.mm"
include "eqcomd.mm"

theorem redvr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ B =/= 0 ) -> ( A ( /r ` RRfld ) B ) = ( A / B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cdiv
    co
    #
    cA
    cB
    crefld
    cdvr
    cfv
    #
    co
    #
    @3
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    cB
    crefld
    cui
    cfv
    #
    wcel
    #
    @4
    @6
    wceq
    @7
    @3
    @7
    crefld
    cdr
    wcel
    #
    resubdrg
    simpli
    a1i
    @0
    @1
    @2
    simp1
    @3
    @1
    @2
    wa
    #
    @9
    @0
    @1
    @2
    3simpc
    @10
    @9
    @11
    wb
    @7
    @10
    resubdrg
    simpri
    cr
    crefld
    @8
    cB
    cc0
    rebase
    @8
    eqid
    #
    re0g
    drngunit
    ax-mp
    sylibr
    cr
    cdiv
    ccnfld
    crefld
    @8
    @5
    cA
    cB
    df-refld
    cnflddiv
    @12
    @5
    eqid
    subrgdv
    syl3anc
    eqcomd
end
