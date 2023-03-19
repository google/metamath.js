include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wrex.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "cgcd.mm"
include "co.mm"
include "wne.mm"
include "wex.mm"
include "eluz2nn.mm"
include "adantr.mm"
include "simpr.mm"
include "eluz2b3.mm"
include "df-ne.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylbi.mm"
include "jca.mm"
include "biimpri.mm"
include "anim1i.mm"
include "ancomd.mm"
include "sylibr.mm"
include "ex.mm"
include "impcom.mm"
include "simprrl.mm"
include "impbid2.mm"
include "exbidv.mm"
include "df-rex.mm"
include "3bitr4g.mm"
include "wb.mm"
include "rexanali.mm"
include "a1i.mm"
include "coprmgcdb.mm"
include "necon3bbid.mm"
include "3bitrd.mm"

theorem ncoprmgcdne1b
  let cA: class A
  let cB: class B
  let vi: setvar i

  disjoint A i
  disjoint B i
  assert |- ( ( A e. NN /\ B e. NN ) -> ( E. i e. ( ZZ>= ` 2 ) ( i || A /\ i || B ) <-> ( A gcd B ) =/= 1 ) )

  proof
    cA
    cn
    wcel
    cB
    cn
    wcel
    wa
    #
    vi
    cv
    #
    cA
    cdvds
    wbr
    @1
    cB
    cdvds
    wbr
    wa
    #
    vi
    c2
    cuz
    cfv
    #
    wrex
    #
    @2
    @1
    c1
    wceq
    #
    wn
    #
    wa
    #
    vi
    cn
    wrex
    #
    @2
    @5
    wi
    vi
    cn
    wral
    #
    wn
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wne
    @0
    @1
    @3
    wcel
    #
    @2
    wa
    #
    vi
    wex
    @1
    cn
    wcel
    #
    @7
    wa
    #
    vi
    wex
    @4
    @8
    @0
    @13
    @15
    vi
    @0
    @13
    @15
    @13
    @14
    @7
    @12
    @14
    @2
    @1
    eluz2nn
    adantr
    @13
    @2
    @6
    @12
    @2
    simpr
    @12
    @6
    @2
    @12
    @14
    @1
    c1
    wne
    #
    wa
    #
    @6
    @1
    eluz2b3
    #
    @16
    @6
    @14
    @16
    @6
    @1
    c1
    df-ne
    #
    biimpi
    adantl
    sylbi
    adantr
    jca
    jca
    @0
    @15
    @13
    @0
    @15
    wa
    @12
    @2
    @15
    @12
    @0
    @7
    @14
    @12
    @6
    @14
    @12
    wi
    @2
    @6
    @14
    @12
    @6
    @14
    wa
    #
    @17
    @12
    @20
    @16
    @14
    @6
    @16
    @14
    @16
    @6
    @19
    biimpri
    anim1i
    ancomd
    @18
    sylibr
    ex
    adantl
    impcom
    adantl
    @0
    @14
    @2
    @6
    simprrl
    jca
    ex
    impbid2
    exbidv
    @2
    vi
    @3
    df-rex
    @7
    vi
    cn
    df-rex
    3bitr4g
    @8
    @10
    wb
    @0
    @2
    @5
    vi
    cn
    rexanali
    a1i
    @0
    @9
    @11
    c1
    cA
    cB
    vi
    coprmgcdb
    necon3bbid
    3bitrd
end
