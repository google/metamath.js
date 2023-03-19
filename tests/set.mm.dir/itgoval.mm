include "cc.mm"
include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "citgo.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wa.mm"
include "cply.mm"
include "wrex.mm"
include "crab.mm"
include "cnex.mm"
include "elpw2.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "rabbidv.mm"
include "df-itgo.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylbir.mm"

theorem itgoval
  let vx: setvar x
  let cS: class S
  let vp: setvar p
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cT: class T

  disjoint S x
  disjoint S p
  disjoint p x
  disjoint S s
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint s x
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint p s
  disjoint a p
  disjoint b p
  disjoint c p
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint T x
  disjoint T p
  disjoint T s
  disjoint T a
  disjoint T b
  disjoint T c
  assert |- ( S C_ CC -> ( IntgOver ` S ) = { x e. CC | E. p e. ( Poly ` S ) ( ( p ` x ) = 0 /\ ( ( coeff ` p ) ` ( deg ` p ) ) = 1 ) } )

  proof
    cS
    cc
    wss
    cS
    cc
    cpw
    #
    wcel
    cS
    citgo
    cfv
    vx
    cv
    vp
    cv
    #
    cfv
    cc0
    wceq
    @1
    cdgr
    cfv
    @1
    ccoe
    cfv
    cfv
    c1
    wceq
    wa
    #
    vp
    cS
    cply
    cfv
    #
    wrex
    #
    vx
    cc
    crab
    #
    wceq
    cS
    cc
    cnex
    elpw2
    vs
    cS
    @2
    vp
    vs
    cv
    #
    cply
    cfv
    #
    wrex
    #
    vx
    cc
    crab
    @5
    @0
    citgo
    @6
    cS
    wceq
    #
    @8
    @4
    vx
    cc
    @9
    @2
    vp
    @7
    @3
    @6
    cS
    cply
    fveq2
    rexeqdv
    rabbidv
    vx
    vs
    vp
    df-itgo
    @4
    vx
    cc
    cnex
    rabex
    fvmpt
    sylbir
end
