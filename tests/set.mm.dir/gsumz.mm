include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cmpt.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "csn.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snid.mm"
include "gsumvallem2.mm"
include "syl5eleqr.mm"
include "ad2antrr.mm"
include "fmptd.mm"
include "gsumval1.mm"

theorem gsumz
  let cA: class A
  let vk: setvar k
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume gsumz.z: |- .0. = ( 0g ` G )

  disjoint A k
  disjoint G k
  disjoint V k
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .0. x
  disjoint .0. y
  assert |- ( ( G e. Mnd /\ A e. V ) -> ( G gsum ( k e. A |-> .0. ) ) = .0. )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    vx
    vy
    cA
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    vk
    cA
    c.0
    cmpt
    #
    cG
    vx
    cv
    #
    vy
    cv
    #
    @4
    co
    @7
    wceq
    @7
    @6
    @4
    co
    @7
    wceq
    wa
    vy
    @3
    wral
    vx
    @3
    crab
    #
    cmnd
    cV
    c.0
    @3
    eqid
    #
    gsumz.z
    @4
    eqid
    #
    @8
    eqid
    #
    @0
    @1
    simpl
    @0
    @1
    simpr
    @2
    vk
    cA
    c.0
    @8
    @5
    @0
    c.0
    @8
    wcel
    @1
    vk
    cv
    cA
    wcel
    @0
    c.0
    c.0
    csn
    @8
    c.0
    c.0
    cG
    c0g
    cfv
    cvv
    gsumz.z
    cG
    c0g
    fvex
    eqeltri
    snid
    vx
    vy
    @3
    @4
    cG
    @8
    c.0
    @9
    gsumz.z
    @10
    @11
    gsumvallem2
    syl5eleqr
    ad2antrr
    @5
    eqid
    fmptd
    gsumval1
end
