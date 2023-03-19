include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wlim.mm"
include "wn.mm"
include "w3a.mm"
include "cuni.mm"
include "csuc.mm"
include "wceq.mm"
include "wo.mm"
include "word.mm"
include "eloni.mm"
include "3ad2ant1.mm"
include "orduniorsuc.mm"
include "syl.mm"
include "orcomd.mm"
include "simp2.mm"
include "wa.mm"
include "df-lim.mm"
include "biimpri.mm"
include "3expb.mm"
include "con3i.mm"
include "3ad2ant3.mm"
include "mpnanrd.mm"
include "wi.mm"
include "orcom.mm"
include "df-or.mm"
include "sylbb.mm"
include "sylc.mm"

theorem onsucuni3
  let cB: class B


  assert |- ( ( B e. On /\ B =/= (/) /\ -. Lim B ) -> B = suc U. B )

  proof
    cB
    con0
    wcel
    #
    cB
    c0
    wne
    #
    cB
    wlim
    #
    wn
    #
    w3a
    #
    cB
    cB
    cuni
    #
    csuc
    wceq
    #
    cB
    @5
    wceq
    #
    wo
    #
    @7
    wn
    #
    @6
    @4
    @7
    @6
    @4
    cB
    word
    #
    @7
    @6
    wo
    #
    @0
    @1
    @10
    @3
    cB
    eloni
    3ad2ant1
    #
    cB
    orduniorsuc
    syl
    orcomd
    @4
    @1
    @7
    @0
    @1
    @3
    simp2
    @4
    @10
    @1
    @7
    wa
    #
    @12
    @3
    @0
    @10
    @13
    wa
    #
    wn
    @1
    @14
    @2
    @10
    @1
    @7
    @2
    @2
    @10
    @1
    @7
    w3a
    cB
    df-lim
    biimpri
    3expb
    con3i
    3ad2ant3
    mpnanrd
    mpnanrd
    @8
    @11
    @9
    @6
    wi
    @6
    @7
    orcom
    @7
    @6
    df-or
    sylbb
    sylc
end
