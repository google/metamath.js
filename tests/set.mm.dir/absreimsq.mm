include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cre.mm"
include "cim.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "syl2an.mm"
include "absvalsq2.mm"
include "syl.mm"
include "crre.mm"
include "oveq1d.mm"
include "crim.mm"
include "oveq12d.mm"
include "eqtrd.mm"

theorem absreimsq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( abs ` ( A + ( _i x. B ) ) ) ^ 2 ) = ( ( A ^ 2 ) + ( B ^ 2 ) ) )

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
    ci
    cB
    cmul
    co
    #
    caddc
    co
    #
    cabs
    cfv
    c2
    cexp
    co
    #
    @4
    cre
    cfv
    #
    c2
    cexp
    co
    #
    @4
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    @2
    @4
    cc
    wcel
    #
    @5
    @10
    wceq
    @0
    cA
    cc
    wcel
    @3
    cc
    wcel
    #
    @13
    @1
    cA
    recn
    @1
    ci
    cc
    wcel
    cB
    cc
    wcel
    @14
    ax-icn
    cB
    recn
    ci
    cB
    mulcl
    sylancr
    cA
    @3
    addcl
    syl2an
    @4
    absvalsq2
    syl
    @2
    @7
    @11
    @9
    @12
    caddc
    @2
    @6
    cA
    c2
    cexp
    cA
    cB
    crre
    oveq1d
    @2
    @8
    cB
    c2
    cexp
    cA
    cB
    crim
    oveq1d
    oveq12d
    eqtrd
end
