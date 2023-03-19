include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "c0v.mm"
include "cva.mm"
include "wceq.mm"
include "chil.mm"
include "shel.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "adantlr.mm"
include "sh0.mm"
include "adantl.mm"
include "shsva.mm"
include "mpan2d.mm"
include "imp.mm"
include "eqeltrrd.mm"
include "ex.mm"

theorem shsel1
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( C e. A -> C e. ( A +H B ) ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    cC
    cA
    wcel
    #
    cC
    cA
    cB
    cph
    co
    #
    wcel
    @2
    @3
    wa
    cC
    c0v
    cva
    co
    #
    cC
    @4
    @0
    @3
    @5
    cC
    wceq
    #
    @1
    @0
    @3
    wa
    cC
    chil
    wcel
    @6
    cC
    cA
    shel
    cC
    ax-hvaddid
    syl
    adantlr
    @2
    @3
    @5
    @4
    wcel
    #
    @2
    @3
    c0v
    cB
    wcel
    #
    @7
    @1
    @8
    @0
    cB
    sh0
    adantl
    cA
    cB
    cC
    c0v
    shsva
    mpan2d
    imp
    eqeltrrd
    ex
end
