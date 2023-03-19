include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wceq.mm"
include "npncan.mm"
include "3com23.mm"
include "fveq2d.mm"
include "wbr.mm"
include "subcl.mm"
include "3adant2.mm"
include "ancoms.mm"
include "3adant1.mm"
include "abstri.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"

theorem abs3dif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( abs ` ( A - B ) ) <_ ( ( abs ` ( A - C ) ) + ( abs ` ( C - B ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cC
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    @4
    cabs
    cfv
    @5
    cabs
    cfv
    caddc
    co
    #
    cle
    @3
    @6
    @8
    cabs
    @0
    @2
    @1
    @6
    @8
    wceq
    cA
    cC
    cB
    npncan
    3com23
    fveq2d
    @3
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @7
    @9
    cle
    wbr
    @0
    @2
    @10
    @1
    cA
    cC
    subcl
    3adant2
    @1
    @2
    @11
    @0
    @2
    @1
    @11
    cC
    cB
    subcl
    ancoms
    3adant1
    @4
    @5
    abstri
    syl2anc
    eqbrtrrd
end
