include "wacn.mm"
include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wex.mm"
include "cvv.mm"
include "pwexg.mm"
include "difexg.mm"
include "syl.mm"
include "acnrcl.mm"
include "elmapd.mm"
include "biimpar.mm"
include "wb.mm"
include "isacn.mm"
include "mpdan.mm"
include "ibi.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "exbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem acni
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let wph: wff ph
  let wps: wff ps
  let cC: class C

  disjoint g x
  disjoint A g
  disjoint A x
  disjoint F g
  disjoint F x
  disjoint X g
  disjoint X x
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g y
  disjoint g z
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint g ph
  disjoint ps y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint X f
  disjoint X h
  disjoint X y
  assert |- ( ( X e. AC_ A /\ F : A --> ( ~P X \ { (/) } ) ) -> E. g A. x e. A ( g ` x ) e. ( F ` x ) )

  proof
    cX
    cA
    wacn
    #
    wcel
    #
    cA
    cX
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cF
    wf
    #
    wa
    cF
    @4
    cA
    cmap
    co
    #
    wcel
    #
    vx
    cv
    #
    vg
    cv
    cfv
    #
    @8
    vf
    cv
    #
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    vg
    wex
    #
    vf
    @6
    wral
    #
    @9
    @8
    cF
    cfv
    #
    wcel
    #
    vx
    cA
    wral
    #
    vg
    wex
    #
    @1
    @7
    @5
    @1
    @4
    cA
    cF
    cvv
    cvv
    @1
    @2
    cvv
    wcel
    @4
    cvv
    wcel
    cX
    @0
    pwexg
    @2
    @3
    cvv
    difexg
    syl
    cA
    cX
    acnrcl
    #
    elmapd
    biimpar
    @1
    @15
    @5
    @1
    @15
    @1
    cA
    cvv
    wcel
    @1
    @15
    wb
    @20
    vx
    cA
    vf
    vg
    @0
    cvv
    cX
    isacn
    mpdan
    ibi
    adantr
    @14
    @19
    vf
    cF
    @6
    @10
    cF
    wceq
    #
    @13
    @18
    vg
    @21
    @12
    @17
    vx
    cA
    @21
    @11
    @16
    @9
    @8
    @10
    cF
    fveq1
    eleq2d
    ralbidv
    exbidv
    rspcv
    sylc
end
