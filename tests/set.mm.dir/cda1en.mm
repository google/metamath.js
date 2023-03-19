include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "enrefg.mm"
include "adantr.mm"
include "ensn1g.mm"
include "ensymd.mm"
include "simpr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cdaenun.mm"
include "syl3anc.mm"
include "df-suc.mm"
include "syl6breqr.mm"

theorem cda1en
  let cA: class A
  let cV: class V


  assert |- ( ( A e. V /\ -. A e. A ) -> ( A +c 1o ) ~~ suc A )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    wcel
    wn
    #
    wa
    #
    cA
    c1o
    ccda
    co
    #
    cA
    cA
    csn
    #
    cun
    #
    cA
    csuc
    cen
    @2
    cA
    cA
    cen
    wbr
    #
    c1o
    @4
    cen
    wbr
    #
    cA
    @4
    cin
    c0
    wceq
    #
    @3
    @5
    cen
    wbr
    @0
    @6
    @1
    cA
    cV
    enrefg
    adantr
    @0
    @7
    @1
    @0
    @4
    c1o
    cA
    cV
    ensn1g
    ensymd
    adantr
    @2
    @1
    @8
    @0
    @1
    simpr
    cA
    cA
    disjsn
    sylibr
    cA
    cA
    c1o
    @4
    cdaenun
    syl3anc
    cA
    df-suc
    syl6breqr
end
