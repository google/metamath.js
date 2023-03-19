include "wcel.mm"
include "c0.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cco.mm"
include "chom.mm"
include "simpr.mm"
include "eqidd.mm"
include "simpl.mm"
include "cv.mm"
include "co.mm"
include "noel.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "w3a.mm"
include "cop.mm"
include "simpr1.mm"
include "syl.mm"
include "simp21.mm"
include "simp2ll.mm"
include "iscatd.mm"

theorem 0catg
  let cC: class C
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( C e. V /\ (/) = ( Base ` C ) ) -> C e. Cat )

  proof
    cC
    cV
    wcel
    #
    c0
    cC
    cbs
    cfv
    wceq
    #
    wa
    #
    vx
    vy
    vz
    vw
    c0
    cC
    cC
    cco
    cfv
    #
    c0
    vf
    vg
    vh
    cC
    chom
    cfv
    #
    cV
    @0
    @1
    simpr
    @2
    @4
    eqidd
    @2
    @3
    eqidd
    @0
    @1
    simpl
    vx
    cv
    #
    c0
    wcel
    #
    c0
    @5
    @5
    @4
    co
    wcel
    #
    @2
    @6
    @7
    @5
    noel
    #
    pm2.21i
    adantl
    @2
    @6
    vy
    cv
    #
    c0
    wcel
    #
    vf
    cv
    #
    @9
    @5
    @4
    co
    wcel
    #
    w3a
    wa
    @6
    c0
    @11
    @9
    @5
    cop
    @5
    @3
    co
    co
    @11
    wceq
    #
    @2
    @6
    @10
    @12
    simpr1
    @6
    @13
    @8
    pm2.21i
    syl
    @2
    @6
    @10
    @11
    @5
    @9
    @4
    co
    wcel
    #
    w3a
    wa
    @6
    @11
    c0
    @5
    @5
    cop
    @9
    @3
    co
    co
    @11
    wceq
    #
    @2
    @6
    @10
    @14
    simpr1
    @6
    @15
    @8
    pm2.21i
    syl
    @2
    @6
    @10
    vz
    cv
    #
    c0
    wcel
    #
    w3a
    @14
    vg
    cv
    #
    @9
    @16
    @4
    co
    wcel
    #
    wa
    #
    w3a
    @6
    @18
    @11
    @5
    @9
    cop
    #
    @16
    @3
    co
    co
    #
    @5
    @16
    @4
    co
    wcel
    #
    @2
    @6
    @10
    @17
    @20
    simp21
    @6
    @23
    @8
    pm2.21i
    syl
    @2
    @6
    @10
    wa
    @17
    vw
    cv
    #
    c0
    wcel
    wa
    #
    wa
    @14
    @19
    vh
    cv
    #
    @16
    @24
    @4
    co
    wcel
    w3a
    #
    w3a
    @6
    @26
    @18
    @9
    @16
    cop
    @24
    @3
    co
    co
    @11
    @21
    @24
    @3
    co
    co
    @26
    @22
    @5
    @16
    cop
    @24
    @3
    co
    co
    wceq
    #
    @6
    @10
    @25
    @2
    @27
    simp2ll
    @6
    @28
    @8
    pm2.21i
    syl
    iscatd
end
