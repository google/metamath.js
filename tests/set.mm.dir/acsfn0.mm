include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "c0.mm"
include "wss.mm"
include "wi.mm"
include "cacs.mm"
include "cfv.mm"
include "0ss.mm"
include "a1bi.mm"
include "rabbii.mm"
include "cfn.mm"
include "0fin.mm"
include "acsfn.mm"
include "mpanr12.mm"
include "syl5eqel.mm"

theorem acsfn0
  let cK: class K
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cT: class T
  let vx: setvar x
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f

  disjoint K a
  disjoint V a
  disjoint X a
  disjoint K b
  disjoint K c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint V b
  disjoint V c
  disjoint X b
  disjoint X c
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint a d
  disjoint a e
  disjoint d e
  disjoint a f
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint e x
  assert |- ( ( X e. V /\ K e. X ) -> { a e. ~P X | K e. a } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    cK
    cX
    wcel
    wa
    #
    cK
    va
    cv
    #
    wcel
    #
    va
    cX
    cpw
    #
    crab
    c0
    @1
    wss
    #
    @2
    wi
    #
    va
    @3
    crab
    #
    cX
    cacs
    cfv
    #
    @2
    @5
    va
    @3
    @4
    @2
    @1
    0ss
    a1bi
    rabbii
    @0
    c0
    cX
    wss
    c0
    cfn
    wcel
    @6
    @7
    wcel
    cX
    0ss
    0fin
    c0
    cK
    cV
    cX
    va
    acsfn
    mpanr12
    syl5eqel
end
