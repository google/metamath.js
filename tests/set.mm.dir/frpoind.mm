include "wfr.mm"
include "wpo.mm"
include "wse.mm"
include "w3a.mm"
include "wss.mm"
include "cv.mm"
include "cpred.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "ssdif0.mm"
include "necon3bbii.mm"
include "difss.mm"
include "wceq.mm"
include "wrex.mm"
include "frpomin2.mm"
include "eldif.mm"
include "anbi1i.mm"
include "anass.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "indif2.mm"
include "df-pred.mm"
include "incom.mm"
include "eqtri.mm"
include "difeq1i.mm"
include "3eqtr4i.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "3bitri.mm"
include "rexbii2.mm"
include "rexanali.mm"
include "sylib.mm"
include "ex.mm"
include "mpani.mm"
include "syl5bi.mm"
include "con4d.mm"
include "imp.mm"
include "adantrl.mm"
include "simprl.mm"
include "eqssd.mm"

theorem frpoind
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( ( ( R Fr A /\ R Po A /\ R Se A ) /\ ( B C_ A /\ A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) ) -> A = B )

  proof
    cA
    cR
    wfr
    cA
    cR
    wpo
    cA
    cR
    wse
    w3a
    #
    cB
    cA
    wss
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    cB
    wss
    #
    @2
    cB
    wcel
    #
    wi
    vy
    cA
    wral
    #
    wa
    wa
    cA
    cB
    @0
    @6
    cA
    cB
    wss
    #
    @1
    @0
    @6
    @7
    @0
    @7
    @6
    @7
    wn
    cA
    cB
    cdif
    #
    c0
    wne
    #
    @0
    @6
    wn
    #
    @7
    @8
    c0
    cA
    cB
    ssdif0
    necon3bbii
    @0
    @8
    cA
    wss
    #
    @9
    @10
    cA
    cB
    difss
    @0
    @11
    @9
    wa
    #
    @10
    @0
    @12
    wa
    @8
    cR
    @2
    cpred
    #
    c0
    wceq
    #
    vy
    @8
    wrex
    #
    @10
    vy
    cA
    @8
    cR
    frpomin2
    @15
    @4
    @5
    wn
    #
    wa
    #
    vy
    cA
    wrex
    @10
    @14
    @17
    vy
    @8
    cA
    @2
    @8
    wcel
    #
    @14
    wa
    @2
    cA
    wcel
    #
    @16
    wa
    #
    @14
    wa
    @19
    @16
    @14
    wa
    #
    wa
    @19
    @17
    wa
    @18
    @20
    @14
    @2
    cA
    cB
    eldif
    anbi1i
    @19
    @16
    @14
    anass
    @21
    @17
    @19
    @21
    @16
    @4
    wa
    @17
    @14
    @4
    @16
    @14
    @3
    cB
    cdif
    #
    c0
    wceq
    @4
    @13
    @22
    c0
    cR
    ccnv
    @2
    csn
    cima
    #
    @8
    cin
    #
    @23
    cA
    cin
    #
    cB
    cdif
    @13
    @22
    @23
    cA
    cB
    indif2
    @13
    @8
    @23
    cin
    @24
    @8
    cR
    @2
    df-pred
    @8
    @23
    incom
    eqtri
    @3
    @25
    cB
    @3
    cA
    @23
    cin
    @25
    cA
    cR
    @2
    df-pred
    cA
    @23
    incom
    eqtri
    difeq1i
    3eqtr4i
    eqeq1i
    @3
    cB
    ssdif0
    bitr4i
    anbi2i
    @16
    @4
    ancom
    bitri
    anbi2i
    3bitri
    rexbii2
    @4
    @5
    vy
    cA
    rexanali
    bitri
    sylib
    ex
    mpani
    syl5bi
    con4d
    imp
    adantrl
    @0
    @1
    @6
    simprl
    eqssd
end
