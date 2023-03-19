include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cva.mm"
include "chil.mm"
include "wss.mm"
include "wceq.mm"
include "choccl.mm"
include "adantl.mm"
include "csh.mm"
include "chsh.mm"
include "shococss.mm"
include "syl.mm"
include "jca.mm"
include "hstosum.mm"
include "mpdan.mm"
include "chjo.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem hstoc
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( ( S ` A ) +h ( S ` ( _|_ ` A ) ) ) = ( S ` ~H ) )

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
    cA
    cort
    cfv
    #
    chj
    co
    #
    cS
    cfv
    #
    cA
    cS
    cfv
    @3
    cS
    cfv
    cva
    co
    #
    chil
    cS
    cfv
    #
    @2
    @3
    cch
    wcel
    #
    cA
    @3
    cort
    cfv
    wss
    #
    wa
    @5
    @6
    wceq
    @2
    @8
    @9
    @1
    @8
    @0
    cA
    choccl
    adantl
    @1
    @9
    @0
    @1
    cA
    csh
    wcel
    @9
    cA
    chsh
    cA
    shococss
    syl
    adantl
    jca
    cA
    @3
    cS
    hstosum
    mpdan
    @1
    @5
    @7
    wceq
    @0
    @1
    @4
    chil
    cS
    cA
    chjo
    fveq2d
    adantl
    eqtr3d
end
