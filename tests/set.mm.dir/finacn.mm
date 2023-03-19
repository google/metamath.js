include "cfn.mm"
include "wcel.mm"
include "wacn.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wex.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "wf.mm"
include "wrex.mm"
include "elmapi.mm"
include "adantl.mm"
include "wne.mm"
include "ffvelrn.mm"
include "eldifsni.mm"
include "syl.mm"
include "n0.mm"
include "sylib.mm"
include "rexv.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "ac6sfi.mm"
include "syldan.mm"
include "exsimpr.mm"
include "wb.mm"
include "vex.mm"
include "isacn.mm"
include "mpan.mm"
include "mpbird.mm"
include "a1i.mm"
include "2thd.mm"
include "eqrdv.mm"

theorem finacn
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cC: class C
  let cX: class X


  assert |- ( A e. Fin -> AC_ A = _V )

  proof
    cA
    cfn
    wcel
    #
    vx
    cA
    wacn
    #
    cvv
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @2
    cvv
    wcel
    #
    @0
    @3
    vy
    cv
    #
    vg
    cv
    #
    cfv
    #
    @5
    vf
    cv
    #
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    vg
    wex
    #
    vf
    @2
    cpw
    #
    c0
    csn
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    @0
    @12
    vf
    @15
    @0
    @8
    @15
    wcel
    #
    wa
    #
    cA
    cvv
    @6
    wf
    #
    @11
    wa
    vg
    wex
    #
    @12
    @0
    @17
    vz
    cv
    #
    @9
    wcel
    #
    vz
    cvv
    wrex
    #
    vy
    cA
    wral
    #
    @20
    @18
    cA
    @14
    @8
    wf
    #
    @24
    @17
    @25
    @0
    @8
    @14
    cA
    elmapi
    adantl
    @25
    @23
    vy
    cA
    @25
    @5
    cA
    wcel
    wa
    #
    @22
    vz
    wex
    #
    @23
    @26
    @9
    c0
    wne
    #
    @27
    @26
    @9
    @14
    wcel
    @28
    cA
    @14
    @5
    @8
    ffvelrn
    @9
    @13
    c0
    eldifsni
    syl
    vz
    @9
    n0
    sylib
    @22
    vz
    rexv
    sylibr
    ralrimiva
    syl
    @22
    @10
    vy
    vz
    cA
    cvv
    vg
    @21
    @7
    @9
    eleq1
    ac6sfi
    syldan
    @19
    @11
    vg
    exsimpr
    syl
    ralrimiva
    @4
    @0
    @3
    @16
    wb
    vx
    vex
    #
    vy
    cA
    vf
    vg
    cvv
    cfn
    @2
    isacn
    mpan
    mpbird
    @4
    @0
    @29
    a1i
    2thd
    eqrdv
end
