include "clly.mm"
include "wceq.mm"
include "cnlly.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "simprl.mm"
include "simpl.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "llyrest.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "restnlly.mm"
include "id.mm"
include "eqtrd.mm"
include "nllyrest.mm"
include "eqtr3d.mm"
include "impbii.mm"

theorem loclly
  let cA: class A
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cJ: class J


  assert |- ( Locally A = A <-> N-Locally A = A )

  proof
    cA
    clly
    #
    cA
    wceq
    #
    cA
    cnlly
    #
    cA
    wceq
    #
    @1
    @2
    @0
    cA
    @1
    vx
    cA
    vj
    @1
    vj
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    @4
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    crest
    co
    #
    @0
    cA
    @9
    @4
    @0
    wcel
    @7
    @10
    @0
    wcel
    @9
    @4
    cA
    @0
    @1
    @5
    @7
    simprl
    @1
    @8
    simpl
    #
    eleqtrrd
    @1
    @5
    @7
    simprr
    cA
    @6
    @4
    llyrest
    syl2anc
    @11
    eleqtrd
    restnlly
    @1
    id
    eqtrd
    @3
    @2
    @0
    cA
    @3
    vx
    cA
    vj
    @3
    @8
    wa
    #
    @10
    @2
    cA
    @12
    @4
    @2
    wcel
    @7
    @10
    @2
    wcel
    @12
    @4
    cA
    @2
    @3
    @5
    @7
    simprl
    @3
    @8
    simpl
    #
    eleqtrrd
    @3
    @5
    @7
    simprr
    cA
    @6
    @4
    nllyrest
    syl2anc
    @13
    eleqtrd
    restnlly
    @3
    id
    eqtr3d
    impbii
end
