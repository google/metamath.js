include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cfv.mm"
include "cort.mm"
include "cva.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "chil.mm"
include "caddc.mm"
include "c1.mm"
include "hstoc.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "csp.mm"
include "cc0.mm"
include "wceq.mm"
include "hstcl.mm"
include "choccl.mm"
include "sylan2.mm"
include "jca.mm"
include "wss.mm"
include "adantl.mm"
include "csh.mm"
include "chsh.mm"
include "shococss.mm"
include "syl.mm"
include "hstorth.mm"
include "mpdan.mm"
include "normpyth.mm"
include "sylc.mm"
include "hst1a.mm"
include "sq1.mm"
include "syl6eq.mm"
include "adantr.mm"
include "3eqtr3d.mm"

theorem hstnmoc
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( ( ( normh ` ( S ` A ) ) ^ 2 ) + ( ( normh ` ( S ` ( _|_ ` A ) ) ) ^ 2 ) ) = 1 )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    #
    cA
    cS
    cfv
    #
    cA
    cort
    cfv
    #
    cS
    cfv
    #
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    chil
    cS
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @3
    cno
    cfv
    c2
    cexp
    co
    @5
    cno
    cfv
    c2
    cexp
    co
    caddc
    co
    #
    c1
    @2
    @7
    @10
    c2
    cexp
    @2
    @6
    @9
    cno
    cA
    cS
    hstoc
    fveq2d
    oveq1d
    @2
    @3
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    @3
    @5
    csp
    co
    cc0
    wceq
    #
    @8
    @12
    wceq
    @2
    @13
    @14
    cA
    cS
    hstcl
    @1
    @0
    @4
    cch
    wcel
    #
    @14
    cA
    choccl
    #
    @4
    cS
    hstcl
    sylan2
    jca
    @2
    @16
    cA
    @4
    cort
    cfv
    wss
    #
    wa
    @15
    @2
    @16
    @18
    @1
    @16
    @0
    @17
    adantl
    @1
    @18
    @0
    @1
    cA
    csh
    wcel
    @18
    cA
    chsh
    cA
    shococss
    syl
    adantl
    jca
    cA
    @4
    cS
    hstorth
    mpdan
    @3
    @5
    normpyth
    sylc
    @0
    @11
    c1
    wceq
    @1
    @0
    @11
    c1
    c2
    cexp
    co
    c1
    @0
    @10
    c1
    c2
    cexp
    cS
    hst1a
    oveq1d
    sq1
    syl6eq
    adantr
    3eqtr3d
end
