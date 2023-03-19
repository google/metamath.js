include "w-bnj15.mm"
include "cuni.mm"
include "wfun.mm"
include "cv.mm"
include "wral.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "bnj1497.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "bnj1311.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "ralrimiva.mm"
include "biid.mm"
include "bnj1383.mm"
include "sylancr.mm"
include "funeqi.mm"
include "sylibr.mm"
include "bnj1498.mm"
include "bnj1422.mm"

theorem bnj60
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  assume bnj60.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj60.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj60.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj60.4: |- F = U. C

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint A g
  disjoint A h
  disjoint d g
  disjoint d h
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g x
  disjoint h x
  disjoint B g
  disjoint B h
  disjoint C g
  disjoint C h
  disjoint G g
  disjoint G h
  disjoint R g
  disjoint R h
  disjoint Y g
  disjoint Y h
  assert |- ( R _FrSe A -> F Fn A )

  proof
    cA
    cR
    w-bnj15
    #
    cF
    cA
    @0
    cC
    cuni
    #
    wfun
    #
    cF
    wfun
    @0
    vg
    cv
    #
    wfun
    vg
    cC
    wral
    #
    @3
    @3
    cdm
    vh
    cv
    #
    cdm
    cin
    #
    cres
    @5
    @6
    cres
    wceq
    #
    vh
    cC
    wral
    #
    vg
    cC
    wral
    #
    @2
    vx
    cA
    cB
    cC
    cR
    vf
    vg
    cG
    cY
    vd
    bnj60.1
    bnj60.2
    bnj60.3
    bnj1497
    @0
    @8
    vg
    cC
    @0
    @3
    cC
    wcel
    #
    wa
    @7
    vh
    cC
    @0
    @10
    @5
    cC
    wcel
    @7
    vx
    cA
    cB
    cC
    @6
    cR
    vf
    vg
    vh
    cG
    cY
    vd
    bnj60.1
    bnj60.2
    bnj60.3
    @6
    eqid
    #
    bnj1311
    3expia
    ralrimiv
    ralrimiva
    @4
    @4
    @9
    wa
    #
    cC
    @6
    vg
    vh
    @4
    biid
    @11
    @12
    biid
    bnj1383
    sylancr
    cF
    @1
    bnj60.4
    funeqi
    sylibr
    vx
    cA
    cB
    cC
    cR
    vf
    cF
    cG
    cY
    vd
    bnj60.1
    bnj60.2
    bnj60.3
    bnj60.4
    bnj1498
    bnj1422
end
