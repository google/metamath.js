include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "domnnzr.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cmulr.mm"
include "eqid.mm"
include "domnring.mm"
include "domnmuln0.mm"
include "abvtrivd.mm"
include "ne0i.mm"
include "syl.mm"
include "jca.mm"
include "co.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "n0.mm"
include "wn.mm"
include "neanior.mm"
include "an4.mm"
include "abvdom.mm"
include "3expib.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "syl5bir.mm"
include "necon4bd.mm"
include "ralrimivva.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "anim2i.mm"
include "isdomn.mm"
include "sylibr.mm"
include "impbii.mm"

theorem abvn0b
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume abvn0b.b: |- A = ( AbsVal ` R )


  assert |- ( R e. Domn <-> ( R e. NzRing /\ A =/= (/) ) )

  proof
    cR
    cdomn
    wcel
    #
    cR
    cnzr
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    @0
    @1
    @2
    cR
    domnnzr
    @0
    vx
    cR
    cbs
    cfv
    #
    vx
    cv
    #
    cR
    c0g
    cfv
    #
    wceq
    cc0
    c1
    cif
    cmpt
    #
    cA
    wcel
    @2
    @0
    vx
    vy
    vz
    cA
    @4
    cR
    cR
    cmulr
    cfv
    #
    @7
    @6
    abvn0b.b
    @4
    eqid
    #
    @6
    eqid
    #
    @7
    eqid
    @8
    eqid
    #
    cR
    domnring
    @4
    cR
    @8
    vy
    cv
    #
    vz
    cv
    #
    @6
    @9
    @11
    @10
    domnmuln0
    abvtrivd
    cA
    @7
    ne0i
    syl
    jca
    @3
    @1
    @12
    @13
    @8
    co
    #
    @6
    wceq
    @12
    @6
    wceq
    @13
    @6
    wceq
    wo
    #
    wi
    #
    vz
    @4
    wral
    vy
    @4
    wral
    #
    wa
    @0
    @2
    @17
    @1
    @2
    @5
    cA
    wcel
    #
    vx
    wex
    @17
    vx
    cA
    n0
    @18
    @17
    vx
    @18
    @16
    vy
    vz
    @4
    @4
    @18
    @12
    @4
    wcel
    #
    @13
    @4
    wcel
    #
    wa
    #
    wa
    #
    @15
    @14
    @6
    @15
    wn
    @12
    @6
    wne
    #
    @13
    @6
    wne
    #
    wa
    #
    @22
    @14
    @6
    wne
    #
    @12
    @6
    @13
    @6
    neanior
    @18
    @21
    @25
    @26
    @21
    @25
    wa
    @19
    @23
    wa
    #
    @20
    @24
    wa
    #
    wa
    @18
    @26
    @19
    @20
    @23
    @24
    an4
    @18
    @27
    @28
    @26
    cA
    @4
    cR
    @8
    @5
    @12
    @13
    @6
    abvn0b.b
    @9
    @10
    @11
    abvdom
    3expib
    syl5bi
    expdimp
    syl5bir
    necon4bd
    ralrimivva
    exlimiv
    sylbi
    anim2i
    vy
    vz
    @4
    cR
    @8
    @6
    @9
    @11
    @10
    isdomn
    sylibr
    impbii
end
