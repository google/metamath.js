include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cxne.mm"
include "cxad.mm"
include "cif.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "cxr.mm"
include "wceq.mm"
include "rexr.mm"
include "xrsdsval.mm"
include "syl2an.mm"
include "rexsub.mm"
include "ancoms.mm"
include "adantr.mm"
include "abssuble0.mm"
include "3expa.mm"
include "eqtr4d.mm"
include "wn.mm"
include "letric.mm"
include "orcanai.mm"
include "abssubge0.mm"
include "3com12.mm"
include "syldan.mm"
include "ifeqda.mm"
include "eqtrd.mm"

theorem xrsdsreval
  let cA: class A
  let cB: class B
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume xrsds.d: |- D = ( dist ` RR*s )


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A D B ) = ( abs ` ( A - B ) ) )

  proof
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
    cA
    cB
    cD
    co
    #
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
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @3
    @7
    wceq
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    cD
    xrsds.d
    xrsdsval
    syl2an
    @2
    @4
    @5
    @6
    @9
    @2
    @4
    wa
    @5
    cB
    cA
    cmin
    co
    #
    @9
    @2
    @5
    @10
    wceq
    #
    @4
    @1
    @0
    @11
    cB
    cA
    rexsub
    ancoms
    adantr
    @0
    @1
    @4
    @9
    @10
    wceq
    cA
    cB
    abssuble0
    3expa
    eqtr4d
    @2
    @4
    wn
    #
    wa
    @6
    @8
    @9
    @2
    @6
    @8
    wceq
    @12
    cA
    cB
    rexsub
    adantr
    @2
    @12
    cB
    cA
    cle
    wbr
    #
    @9
    @8
    wceq
    #
    @2
    @4
    @13
    cA
    cB
    letric
    orcanai
    @0
    @1
    @13
    @14
    @1
    @0
    @13
    @14
    cB
    cA
    abssubge0
    3com12
    3expa
    syldan
    eqtr4d
    ifeqda
    eqtrd
end
