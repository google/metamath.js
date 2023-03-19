include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cre.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "recn.mm"
include "immul.mm"
include "sylan.mm"
include "rere.mm"
include "adantr.mm"
include "oveq1d.mm"
include "reim0.mm"
include "recl.mm"
include "recnd.mm"
include "mul02d.mm"
include "sylan9eq.mm"
include "oveq12d.mm"
include "imcl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "addid1d.mm"
include "3eqtrd.mm"

theorem immul2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. CC ) -> ( Im ` ( A x. B ) ) = ( A x. ( Im ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    cim
    cfv
    #
    cA
    cre
    cfv
    #
    cB
    cim
    cfv
    #
    cmul
    co
    #
    cA
    cim
    cfv
    #
    cB
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cA
    @5
    cmul
    co
    #
    cc0
    caddc
    co
    @11
    @0
    cA
    cc
    wcel
    #
    @1
    @3
    @10
    wceq
    cA
    recn
    #
    cA
    cB
    immul
    sylan
    @2
    @6
    @11
    @9
    cc0
    caddc
    @2
    @4
    cA
    @5
    cmul
    @0
    @4
    cA
    wceq
    @1
    cA
    rere
    adantr
    oveq1d
    @0
    @1
    @9
    cc0
    @8
    cmul
    co
    cc0
    @0
    @7
    cc0
    @8
    cmul
    cA
    reim0
    oveq1d
    @1
    @8
    @1
    @8
    cB
    recl
    recnd
    mul02d
    sylan9eq
    oveq12d
    @2
    @11
    @0
    @12
    @5
    cc
    wcel
    @11
    cc
    wcel
    @1
    @13
    @1
    @5
    cB
    imcl
    recnd
    cA
    @5
    mulcl
    syl2an
    addid1d
    3eqtrd
end
