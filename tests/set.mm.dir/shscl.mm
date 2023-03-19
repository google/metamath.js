include "csh.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "helsh.mm"
include "elimel.mm"
include "shscli.mm"
include "dedth2h.mm"

theorem shscl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A +H B ) e. SH )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cA
    cB
    cph
    co
    #
    csh
    wcel
    @0
    cA
    chil
    cif
    #
    cB
    cph
    co
    #
    csh
    wcel
    @3
    @1
    cB
    chil
    cif
    #
    cph
    co
    #
    csh
    wcel
    cA
    cB
    chil
    chil
    cA
    @3
    wceq
    @2
    @4
    csh
    cA
    @3
    cB
    cph
    oveq1
    eleq1d
    cB
    @5
    wceq
    @4
    @6
    csh
    cB
    @5
    @3
    cph
    oveq2
    eleq1d
    @3
    @5
    cA
    chil
    csh
    helsh
    elimel
    cB
    chil
    csh
    helsh
    elimel
    shscli
    dedth2h
end
