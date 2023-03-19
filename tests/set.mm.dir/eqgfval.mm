include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "cqg.mm"
include "cminusg.mm"
include "cplusg.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "sseq2d.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "simpr.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "df-eqg.mm"
include "cxp.mm"
include "xpex.mm"
include "vex.mm"
include "prss.mm"
include "sylibr.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "ovmpt2a.mm"
include "syl5eq.mm"
include "syl2an.mm"

theorem eqgfval
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cA: class A
  let cB: class B
  let vg: setvar g
  let vs: setvar s
  assume eqgval.x: |- X = ( Base ` G )
  assume eqgval.n: |- N = ( invg ` G )
  assume eqgval.p: |- .+ = ( +g ` G )
  assume eqgval.r: |- R = ( G ~QG S )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint S x
  disjoint S y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint N g
  disjoint N s
  disjoint S g
  disjoint S s
  disjoint .+ g
  disjoint .+ s
  disjoint X g
  disjoint X s
  assert |- ( ( G e. V /\ S C_ X ) -> R = { <. x , y >. | ( { x , y } C_ X /\ ( ( N ` x ) .+ y ) e. S ) } )

  proof
    cG
    cV
    wcel
    cG
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    cR
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cX
    wss
    #
    @2
    cN
    cfv
    #
    @3
    c.pl
    co
    #
    cS
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    wceq
    cS
    cX
    wss
    cG
    cV
    elex
    cS
    cX
    cX
    cG
    cbs
    cfv
    #
    cvv
    eqgval.x
    cG
    cbs
    fvex
    eqeltri
    #
    ssex
    @0
    @1
    wa
    cR
    cG
    cS
    cqg
    co
    @10
    eqgval.r
    vg
    vs
    cG
    cS
    cvv
    cvv
    @4
    vg
    cv
    #
    cbs
    cfv
    #
    wss
    #
    @2
    @13
    cminusg
    cfv
    #
    cfv
    #
    @3
    @13
    cplusg
    cfv
    #
    co
    #
    vs
    cv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @10
    cqg
    @13
    cG
    wceq
    #
    @20
    cS
    wceq
    #
    wa
    #
    @22
    @9
    vx
    vy
    @25
    @15
    @5
    @21
    @8
    @25
    @14
    cX
    @4
    @25
    @14
    @11
    cX
    @25
    @13
    cG
    cbs
    @23
    @24
    simpl
    #
    fveq2d
    eqgval.x
    syl6eqr
    sseq2d
    @25
    @19
    @7
    @20
    cS
    @25
    @17
    @6
    @3
    @3
    @18
    c.pl
    @25
    @18
    cG
    cplusg
    cfv
    c.pl
    @25
    @13
    cG
    cplusg
    @26
    fveq2d
    eqgval.p
    syl6eqr
    @25
    @2
    @16
    cN
    @25
    @16
    cG
    cminusg
    cfv
    cN
    @25
    @13
    cG
    cminusg
    @26
    fveq2d
    eqgval.n
    syl6eqr
    fveq1d
    @25
    @3
    eqidd
    oveq123d
    @23
    @24
    simpr
    eleq12d
    anbi12d
    opabbidv
    vx
    vy
    vs
    vg
    df-eqg
    @10
    cX
    cX
    cxp
    #
    cX
    cX
    @12
    @12
    xpex
    @10
    @2
    cX
    wcel
    @3
    cX
    wcel
    wa
    #
    vx
    vy
    copab
    @27
    @9
    @28
    vx
    vy
    @9
    @5
    @28
    @5
    @8
    simpl
    @2
    @3
    cX
    vx
    vex
    vy
    vex
    prss
    sylibr
    ssopab2i
    vx
    vy
    cX
    cX
    df-xp
    sseqtr4i
    ssexi
    ovmpt2a
    syl5eq
    syl2an
end
