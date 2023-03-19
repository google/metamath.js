include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "ciin.mm"
include "cin.mm"
include "cacs.mm"
include "cfv.mm"
include "riinrab.mm"
include "cmre.mm"
include "mreacs.mm"
include "adantr.mm"
include "acsfn1.mm"
include "ex.mm"
include "ralimdv.mm"
include "imp.mm"
include "mreriincl.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem acsfn1c
  let cE: class E
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
  disjoint K b
  disjoint K c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint E a
  disjoint T a
  disjoint T b
  disjoint T c
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
  assert |- ( ( X e. V /\ A. b e. K A. c e. X E e. X ) -> { a e. ~P X | A. b e. K A. c e. a E e. a } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cE
    cX
    wcel
    vc
    cX
    wral
    #
    vb
    cK
    wral
    #
    wa
    #
    cE
    va
    cv
    #
    wcel
    vc
    @4
    wral
    #
    vb
    cK
    wral
    va
    cX
    cpw
    #
    crab
    @6
    vb
    cK
    @5
    va
    @6
    crab
    #
    ciin
    cin
    #
    cX
    cacs
    cfv
    #
    @5
    vb
    va
    @6
    cK
    riinrab
    @3
    @9
    @6
    cmre
    cfv
    wcel
    #
    @7
    @9
    wcel
    #
    vb
    cK
    wral
    #
    @8
    @9
    wcel
    @0
    @10
    @2
    cV
    cX
    mreacs
    adantr
    @0
    @2
    @12
    @0
    @1
    @11
    vb
    cK
    @0
    @1
    @11
    cE
    cV
    cX
    va
    vc
    acsfn1
    ex
    ralimdv
    imp
    vb
    @9
    @7
    cK
    @6
    mreriincl
    syl2anc
    syl5eqelr
end
