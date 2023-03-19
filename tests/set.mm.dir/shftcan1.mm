include "cc.mm"
include "wcel.mm"
include "cshi.mm"
include "co.mm"
include "cneg.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "wceq.mm"
include "negcl.mm"
include "2shfti.mm"
include "mpdan.mm"
include "negid.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "shftidt.mm"
include "sylan9eq.mm"

theorem shftcan1
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( ( F shift A ) shift -u A ) ` B ) = ( F ` B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    cB
    cF
    cA
    cshi
    co
    cA
    cneg
    #
    cshi
    co
    #
    cfv
    cB
    cF
    cc0
    cshi
    co
    #
    cfv
    cB
    cF
    cfv
    @0
    cB
    @2
    @3
    @0
    @2
    cF
    cA
    @1
    caddc
    co
    #
    cshi
    co
    #
    @3
    @0
    @1
    cc
    wcel
    @2
    @5
    wceq
    cA
    negcl
    cA
    @1
    cF
    shftfval.1
    2shfti
    mpdan
    @0
    @4
    cc0
    cF
    cshi
    cA
    negid
    oveq2d
    eqtrd
    fveq1d
    cB
    cF
    shftfval.1
    shftidt
    sylan9eq
end
