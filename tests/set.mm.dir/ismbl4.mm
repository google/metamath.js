include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "covol.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "ismbl3.mm"
include "cxr.mm"
include "elpwi.mm"
include "ovolcl.mm"
include "syl.mm"
include "adantr.mm"
include "inss1.mm"
include "syl5ss.mm"
include "ssdifssd.mm"
include "xaddcld.mm"
include "ovolsplit.mm"
include "simpr.mm"
include "xrletrid.mm"
include "ex.mm"
include "xrleid.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "impbid.mm"
include "ralbiia.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ismbl4
  let vx: setvar x
  let cA: class A
  let vk: setvar k

  disjoint A x
  disjoint k x
  assert |- ( A e. dom vol <-> ( A C_ RR /\ A. x e. ~P RR ( vol* ` x ) = ( ( vol* ` ( x i^i A ) ) +e ( vol* ` ( x \ A ) ) ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    cA
    cr
    wss
    #
    vx
    cv
    #
    cA
    cin
    #
    covol
    cfv
    #
    @1
    cA
    cdif
    #
    covol
    cfv
    #
    cxad
    co
    #
    @1
    covol
    cfv
    #
    cle
    wbr
    #
    vx
    cr
    cpw
    #
    wral
    #
    wa
    @0
    @7
    @6
    wceq
    #
    vx
    @9
    wral
    #
    wa
    vx
    cA
    ismbl3
    @10
    @12
    @0
    @8
    @11
    vx
    @9
    @1
    @9
    wcel
    #
    @8
    @11
    @13
    @8
    @11
    @13
    @8
    wa
    @7
    @6
    @13
    @7
    cxr
    wcel
    #
    @8
    @13
    @1
    cr
    wss
    @14
    @1
    cr
    elpwi
    #
    @1
    ovolcl
    syl
    adantr
    @13
    @6
    cxr
    wcel
    #
    @8
    @13
    @3
    @5
    @13
    @2
    cr
    wss
    @3
    cxr
    wcel
    @13
    @2
    @1
    cr
    @1
    cA
    inss1
    @15
    syl5ss
    @2
    ovolcl
    syl
    @13
    @4
    cr
    wss
    @5
    cxr
    wcel
    @13
    @1
    cr
    cA
    @15
    ssdifssd
    @4
    ovolcl
    syl
    xaddcld
    #
    adantr
    @13
    @7
    @6
    cle
    wbr
    @8
    @13
    @1
    cA
    @15
    ovolsplit
    adantr
    @13
    @8
    simpr
    xrletrid
    ex
    @13
    @11
    @8
    @13
    @11
    wa
    @6
    @6
    @7
    cle
    @13
    @6
    @6
    cle
    wbr
    #
    @11
    @13
    @16
    @18
    @17
    @6
    xrleid
    syl
    adantr
    @11
    @6
    @7
    wceq
    @13
    @11
    @7
    @6
    @11
    id
    eqcomd
    adantl
    breqtrd
    ex
    impbid
    ralbiia
    anbi2i
    bitri
end
