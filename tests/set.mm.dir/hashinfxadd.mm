include "chash.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cn0.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wnel.mm"
include "w3a.mm"
include "cxad.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "hashnn0pnf.mm"
include "df-nel.mm"
include "anbi2i.mm"
include "pm5.61.mm"
include "sylbb.mm"
include "ex.mm"
include "orcoms.mm"
include "syl.mm"
include "imp.mm"
include "3adant2.mm"
include "oveq1.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "hashxrcl.mm"
include "hashnemnf.mm"
include "jca.mm"
include "3ad2ant2.mm"
include "xaddpnf2.mm"
include "sylan9eqr.mm"
include "expcom.mm"
include "adantr.mm"
include "mpcom.mm"

theorem hashinfxadd
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W /\ ( # ` A ) e/ NN0 ) -> ( ( # ` A ) +e ( # ` B ) ) = +oo )

  proof
    cA
    chash
    cfv
    #
    cpnf
    wceq
    #
    @0
    cn0
    wcel
    #
    wn
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
    @0
    cn0
    wnel
    #
    w3a
    #
    @0
    cB
    chash
    cfv
    #
    cxad
    co
    #
    cpnf
    wceq
    #
    @5
    @7
    @4
    @6
    @5
    @7
    @4
    @5
    @2
    @1
    wo
    @7
    @4
    wi
    #
    cA
    cV
    hashnn0pnf
    @1
    @2
    @12
    @1
    @2
    wo
    #
    @7
    @4
    @13
    @7
    wa
    @13
    @3
    wa
    @4
    @7
    @3
    @13
    @0
    cn0
    df-nel
    anbi2i
    @1
    @2
    pm5.61
    sylbb
    ex
    orcoms
    syl
    imp
    3adant2
    @1
    @8
    @11
    wi
    @3
    @8
    @1
    @11
    @1
    @8
    @10
    cpnf
    @9
    cxad
    co
    #
    cpnf
    @0
    cpnf
    @9
    cxad
    oveq1
    @8
    @9
    cxr
    wcel
    #
    @9
    cmnf
    wne
    #
    wa
    #
    @14
    cpnf
    wceq
    @6
    @5
    @17
    @7
    @6
    @15
    @16
    cB
    cW
    hashxrcl
    cB
    cW
    hashnemnf
    jca
    3ad2ant2
    @9
    xaddpnf2
    syl
    sylan9eqr
    expcom
    adantr
    mpcom
end
