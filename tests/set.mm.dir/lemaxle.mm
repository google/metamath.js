include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "max2.mm"
include "ancoms.mm"
include "adantr.mm"
include "wi.mm"
include "simpr.mm"
include "simpll.mm"
include "ifcl.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "3impia.mm"

theorem lemaxle
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( B e. RR /\ C e. RR ) /\ A e. RR /\ A <_ B ) -> A <_ if ( C <_ B , B , C ) )

  proof
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    cA
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cC
    cB
    cle
    wbr
    #
    cB
    cC
    cif
    #
    cle
    wbr
    #
    @2
    @3
    wa
    #
    @4
    cB
    @6
    cle
    wbr
    #
    @7
    @2
    @9
    @3
    @1
    @0
    @9
    cC
    cB
    max2
    ancoms
    adantr
    @8
    @3
    @0
    @6
    cr
    wcel
    #
    @4
    @9
    wa
    @7
    wi
    @2
    @3
    simpr
    @0
    @1
    @3
    simpll
    @2
    @10
    @3
    @5
    cB
    cC
    cr
    ifcl
    adantr
    cA
    cB
    @6
    letr
    syl3anc
    mpan2d
    3impia
end
