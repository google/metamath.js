include "chil.mm"
include "wcel.mm"
include "cc.mm"
include "cbr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "clf.mm"
include "brafn.mm"
include "wa.mm"
include "simpll.mm"
include "hvmulcl.mm"
include "ad2ant2lr.mm"
include "simprr.mm"
include "braadd.mm"
include "syl3anc.mm"
include "bramul.mm"
include "3expa.mm"
include "adantrr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "ralrimivva.mm"
include "ralrimiva.mm"
include "ellnfn.mm"
include "sylanbrc.mm"

theorem bralnfn
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T


  assert |- ( A e. ~H -> ( bra ` A ) e. LinFn )

  proof
    cA
    chil
    wcel
    #
    chil
    cc
    cA
    cbr
    cfv
    #
    wf
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    @1
    cfv
    #
    @2
    @3
    @1
    cfv
    cmul
    co
    #
    @5
    @1
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    #
    vx
    cc
    wral
    @1
    clf
    wcel
    cA
    brafn
    @0
    @11
    vx
    cc
    @0
    @2
    cc
    wcel
    #
    wa
    #
    @10
    vy
    vz
    chil
    chil
    @13
    @3
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    wa
    #
    @6
    @4
    @1
    cfv
    #
    @8
    caddc
    co
    #
    @9
    @17
    @0
    @4
    chil
    wcel
    #
    @15
    @6
    @19
    wceq
    @0
    @12
    @16
    simpll
    @12
    @14
    @20
    @0
    @15
    @2
    @3
    hvmulcl
    ad2ant2lr
    @13
    @14
    @15
    simprr
    cA
    @4
    @5
    braadd
    syl3anc
    @17
    @18
    @7
    @8
    caddc
    @13
    @14
    @18
    @7
    wceq
    #
    @15
    @0
    @12
    @14
    @21
    cA
    @2
    @3
    bramul
    3expa
    adantrr
    oveq1d
    eqtrd
    ralrimivva
    ralrimiva
    vx
    vy
    vz
    @1
    ellnfn
    sylanbrc
end
