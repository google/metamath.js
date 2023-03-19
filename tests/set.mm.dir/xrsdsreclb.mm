include "cxr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "cr.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "cif.mm"
include "wceq.mm"
include "xrsdsval.mm"
include "3adant3.mm"
include "eleq1d.mm"
include "wi.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "xrsdsreclblem.mm"
include "wn.mm"
include "wo.mm"
include "xrletri.mm"
include "orcanai.mm"
include "necom.mm"
include "3anbi3i.mm"
include "3ancoma.mm"
include "bitri.mm"
include "sylanb.mm"
include "ancom.mm"
include "syl6ib.mm"
include "syldan.mm"
include "ifbothda.mm"
include "sylbid.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "xrsdsreval.mm"
include "cc.mm"
include "recn.mm"
include "subcl.mm"
include "syl2an.mm"
include "abscld.mm"
include "eqeltrd.mm"
include "impbid1.mm"

theorem xrsdsreclb
  let cA: class A
  let cB: class B
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume xrsds.d: |- D = ( dist ` RR*s )


  assert |- ( ( A e. RR* /\ B e. RR* /\ A =/= B ) -> ( ( A D B ) e. RR <-> ( A e. RR /\ B e. RR ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cD
    co
    #
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    @3
    @5
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cxne
    cxad
    co
    #
    cA
    cB
    cxne
    cxad
    co
    #
    cif
    #
    cr
    wcel
    #
    @8
    @3
    @4
    @12
    cr
    @0
    @1
    @4
    @12
    wceq
    @2
    cA
    cB
    cD
    xrsds.d
    xrsdsval
    3adant3
    eleq1d
    @9
    @10
    cr
    wcel
    #
    @8
    wi
    @11
    cr
    wcel
    #
    @8
    wi
    #
    @13
    @8
    wi
    @3
    @10
    @11
    @10
    @12
    wceq
    @14
    @13
    @8
    @10
    @12
    cr
    eleq1
    imbi1d
    @11
    @12
    wceq
    @15
    @13
    @8
    @11
    @12
    cr
    eleq1
    imbi1d
    cA
    cB
    cD
    xrsds.d
    xrsdsreclblem
    @3
    @9
    wn
    cB
    cA
    cle
    wbr
    #
    @16
    @3
    @9
    @17
    @0
    @1
    @9
    @17
    wo
    @2
    cA
    cB
    xrletri
    3adant3
    orcanai
    @3
    @17
    wa
    @15
    @7
    @6
    wa
    #
    @8
    @3
    @1
    @0
    cB
    cA
    wne
    #
    w3a
    #
    @17
    @15
    @18
    wi
    @3
    @0
    @1
    @19
    w3a
    @20
    @2
    @19
    @0
    @1
    cA
    cB
    necom
    3anbi3i
    @0
    @1
    @19
    3ancoma
    bitri
    cB
    cA
    cD
    xrsds.d
    xrsdsreclblem
    sylanb
    @7
    @6
    ancom
    syl6ib
    syldan
    ifbothda
    sylbid
    @8
    @4
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    cr
    cA
    cB
    cD
    xrsds.d
    xrsdsreval
    @8
    @21
    @6
    cA
    cc
    wcel
    cB
    cc
    wcel
    @21
    cc
    wcel
    @7
    cA
    recn
    cB
    recn
    cA
    cB
    subcl
    syl2an
    abscld
    eqeltrd
    impbid1
end
