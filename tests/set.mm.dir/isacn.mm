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
include "wceq.mm"
include "pweq.mm"
include "difeq1d.mm"
include "oveq1d.mm"
include "raleqdv.mm"
include "anbi2d.mm"
include "df-acn.mm"
include "elab2g.mm"
include "wb.mm"
include "elex.mm"
include "biid.mm"
include "baib.mm"
include "syl.mm"
include "sylan9bb.mm"

theorem isacn
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cV: class V
  let cW: class W
  let cX: class X
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cC: class C

  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint X f
  disjoint X g
  disjoint X x
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
  disjoint B g
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
  disjoint X h
  disjoint X y
  assert |- ( ( X e. V /\ A e. W ) -> ( X e. AC_ A <-> A. f e. ( ( ~P X \ { (/) } ) ^m A ) E. g A. x e. A ( g ` x ) e. ( f ` x ) ) )

  proof
    cX
    cV
    wcel
    cX
    cA
    wacn
    #
    wcel
    cA
    cvv
    wcel
    #
    vx
    cv
    #
    vg
    cv
    cfv
    @2
    vf
    cv
    cfv
    wcel
    vx
    cA
    wral
    vg
    wex
    #
    vf
    cX
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    wa
    #
    cA
    cW
    wcel
    #
    @8
    @1
    @3
    vf
    vy
    cv
    #
    cpw
    #
    @5
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    wa
    @9
    vy
    cX
    @0
    cV
    @11
    cX
    wceq
    #
    @15
    @8
    @1
    @16
    @3
    vf
    @14
    @7
    @16
    @13
    @6
    cA
    cmap
    @16
    @12
    @4
    @5
    @11
    cX
    pweq
    difeq1d
    oveq1d
    raleqdv
    anbi2d
    vy
    vx
    cA
    vf
    vg
    df-acn
    elab2g
    @10
    @1
    @9
    @8
    wb
    cA
    cW
    elex
    @9
    @1
    @8
    @9
    biid
    baib
    syl
    sylan9bb
end
