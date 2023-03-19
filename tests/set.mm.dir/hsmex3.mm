include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "csn.mm"
include "ctc.mm"
include "cfv.mm"
include "wral.mm"
include "cab.mm"
include "cdom.mm"
include "wss.mm"
include "cvv.mm"
include "sdomdom.mm"
include "ralimi.mm"
include "ss2abi.mm"
include "hsmex2.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem hsmex3
  let vx: setvar x
  let cV: class V
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z

  disjoint s x
  disjoint X s
  disjoint X x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c s
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint d e
  disjoint d f
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint X d
  disjoint e f
  disjoint e s
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint X e
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint X f
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  assert |- ( X e. V -> { s | A. x e. ( TC ` { s } ) x ~< X } e. _V )

  proof
    cX
    cV
    wcel
    vx
    cv
    #
    cX
    csdm
    wbr
    #
    vx
    vs
    cv
    csn
    ctc
    cfv
    #
    wral
    #
    vs
    cab
    #
    @0
    cX
    cdom
    wbr
    #
    vx
    @2
    wral
    #
    vs
    cab
    #
    wss
    @7
    cvv
    wcel
    @4
    cvv
    wcel
    @3
    @6
    vs
    @1
    @5
    vx
    @2
    @0
    cX
    sdomdom
    ralimi
    ss2abi
    vx
    cV
    cX
    vs
    hsmex2
    @4
    @7
    cvv
    ssexg
    sylancr
end
