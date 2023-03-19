include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "wi.mm"
include "rexr.mm"
include "xleadd1a.mm"
include "ex.mm"
include "syl3an3.mm"
include "cxne.mm"
include "simp1.mm"
include "3ad2ant3.mm"
include "xaddcl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "xnegcl.mm"
include "syl.mm"
include "syl3anc.mm"
include "wceq.mm"
include "xpncan.mm"
include "3adant2.mm"
include "3adant1.mm"
include "breq12d.mm"
include "sylibd.mm"
include "impbid.mm"

theorem xleadd1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR ) -> ( A <_ B <-> ( A +e C ) <_ ( B +e C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    cxad
    co
    #
    cB
    cC
    cxad
    co
    #
    cle
    wbr
    #
    @2
    @0
    @1
    cC
    cxr
    wcel
    #
    @4
    @7
    wi
    cC
    rexr
    #
    @0
    @1
    @8
    w3a
    @4
    @7
    cA
    cB
    cC
    xleadd1a
    ex
    syl3an3
    @3
    @7
    @5
    cC
    cxne
    #
    cxad
    co
    #
    @6
    @10
    cxad
    co
    #
    cle
    wbr
    #
    @4
    @3
    @5
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @10
    cxr
    wcel
    #
    @7
    @13
    wi
    @3
    @0
    @8
    @14
    @0
    @1
    @2
    simp1
    @2
    @0
    @8
    @1
    @9
    3ad2ant3
    #
    cA
    cC
    xaddcl
    syl2anc
    @3
    @1
    @8
    @15
    @0
    @1
    @2
    simp2
    @17
    cB
    cC
    xaddcl
    syl2anc
    @3
    @8
    @16
    @17
    cC
    xnegcl
    syl
    @14
    @15
    @16
    w3a
    @7
    @13
    @5
    @6
    @10
    xleadd1a
    ex
    syl3anc
    @3
    @11
    cA
    @12
    cB
    cle
    @0
    @2
    @11
    cA
    wceq
    @1
    cA
    cC
    xpncan
    3adant2
    @1
    @2
    @12
    cB
    wceq
    @0
    cB
    cC
    xpncan
    3adant1
    breq12d
    sylibd
    impbid
end
