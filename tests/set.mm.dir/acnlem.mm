include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "cvv.mm"
include "wex.mm"
include "crn.mm"
include "cuni.mm"
include "wf.mm"
include "fvssunirn.mm"
include "simpr.mm"
include "sseldi.mm"
include "ralimiaa.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "id.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "fex2.mm"
include "mp3an3.mm"
include "syl2anr.mm"
include "fvmpt2.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "wceq.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbid.mm"
include "spcegv.mm"
include "sylc.mm"

theorem acnlem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cC: class C
  let cX: class X

  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint B g
  disjoint f h
  disjoint f y
  disjoint f z
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
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint g ph
  disjoint ps y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X x
  disjoint X y
  assert |- ( ( A e. V /\ A. x e. A B e. ( f ` x ) ) -> E. g A. x e. A ( g ` x ) e. ( f ` x ) )

  proof
    cA
    cV
    wcel
    #
    cB
    vx
    cv
    #
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
    wa
    vx
    cA
    cB
    cmpt
    #
    cvv
    wcel
    #
    @1
    @6
    cfv
    #
    @3
    wcel
    #
    vx
    cA
    wral
    #
    @1
    vg
    cv
    #
    cfv
    #
    @3
    wcel
    #
    vx
    cA
    wral
    #
    vg
    wex
    @5
    cA
    @2
    crn
    #
    cuni
    #
    @6
    wf
    #
    @0
    @7
    @0
    @5
    cB
    @16
    wcel
    #
    vx
    cA
    wral
    @17
    @4
    @18
    vx
    cA
    @1
    cA
    wcel
    #
    @4
    wa
    #
    @3
    @16
    cB
    @2
    @1
    fvssunirn
    @19
    @4
    simpr
    #
    sseldi
    ralimiaa
    vx
    cA
    @16
    cB
    @6
    @6
    eqid
    #
    fmpt
    sylib
    @0
    id
    @17
    @0
    @16
    cvv
    wcel
    @7
    @15
    @2
    vf
    vex
    rnex
    uniex
    cA
    @16
    @6
    cV
    cvv
    fex2
    mp3an3
    syl2anr
    @5
    @10
    @0
    @4
    @9
    vx
    cA
    @20
    @8
    cB
    @3
    vx
    cA
    cB
    @3
    @6
    @22
    fvmpt2
    @21
    eqeltrd
    ralimiaa
    adantl
    @14
    @10
    vg
    @6
    cvv
    @11
    @6
    wceq
    #
    @13
    @9
    vx
    cA
    vx
    @11
    @6
    vx
    cA
    cB
    nfmpt1
    nfeq2
    @23
    @12
    @8
    @3
    @1
    @11
    @6
    fveq1
    eleq1d
    ralbid
    spcegv
    sylc
end
