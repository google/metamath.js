include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "zcn.mm"
include "negsub.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "znegcl.mm"
include "fladdz.mm"
include "sylan2.mm"
include "reflcl.mm"
include "recnd.mm"
include "3eqtrd.mm"

theorem flsubz
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ N e. ZZ ) -> ( |_ ` ( A - N ) ) = ( ( |_ ` A ) - N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    cmin
    co
    #
    cfl
    cfv
    cA
    cN
    cneg
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cA
    cfl
    cfv
    #
    @4
    caddc
    co
    #
    @7
    cN
    cmin
    co
    #
    @2
    @3
    @5
    cfl
    @2
    @5
    @3
    @0
    cA
    cc
    wcel
    cN
    cc
    wcel
    #
    @5
    @3
    wceq
    @1
    cA
    recn
    cN
    zcn
    #
    cA
    cN
    negsub
    syl2an
    eqcomd
    fveq2d
    @1
    @0
    @4
    cz
    wcel
    @6
    @8
    wceq
    cN
    znegcl
    cA
    @4
    fladdz
    sylan2
    @0
    @7
    cc
    wcel
    @10
    @8
    @9
    wceq
    @1
    @0
    @7
    cA
    reflcl
    recnd
    @11
    @7
    cN
    negsub
    syl2an
    3eqtrd
end
