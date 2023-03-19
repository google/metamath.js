include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "cres.mm"
include "wne.mm"
include "wfn.mm"
include "wrex.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "abid.mm"
include "bnj1238.mm"
include "eqid.mm"
include "bnj1234.mm"
include "eleq2s.mm"
include "bnj770.mm"

theorem bnj1256
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cY: class Y
  let vd: setvar d
  assume bnj1256.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1256.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1256.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1256.4: |- D = ( dom g i^i dom h )
  assume bnj1256.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1256.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1256.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )

  disjoint A f
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint G f
  disjoint G g
  disjoint R f
  disjoint Y g
  disjoint d f
  disjoint d g
  disjoint f x
  disjoint g x
  assert |- ( ph -> E. d e. B g Fn d )

  proof
    cA
    cR
    w-bnj15
    vg
    cv
    #
    cC
    wcel
    vh
    cv
    #
    cC
    wcel
    @0
    cD
    cres
    @1
    cD
    cres
    wne
    @0
    vd
    cv
    #
    wfn
    #
    vd
    cB
    wrex
    #
    wph
    bnj1256.6
    @4
    @0
    @3
    vx
    cv
    #
    @0
    cfv
    @5
    @0
    cA
    cR
    @5
    c-bnj14
    cres
    cop
    #
    cG
    cfv
    wceq
    vx
    @2
    wral
    #
    wa
    vd
    cB
    wrex
    #
    vg
    cab
    #
    cC
    @0
    @9
    wcel
    @3
    @7
    vd
    cB
    @8
    vg
    abid
    bnj1238
    vx
    cA
    cB
    cC
    @9
    cR
    vf
    vg
    cG
    cY
    @6
    vd
    bnj1256.2
    bnj1256.3
    @6
    eqid
    @9
    eqid
    bnj1234
    eleq2s
    bnj770
end
