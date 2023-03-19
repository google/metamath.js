include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "w-bnj15.mm"
include "cres.mm"
include "wne.mm"
include "bnj1247.mm"
include "bnj1234.mm"
include "syl6eleq.mm"
include "wfn.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "abeq2i.mm"
include "bnj1238.mm"
include "bnj1196.mm"
include "c-bnj14.mm"
include "simplbi.mm"
include "fndm.mm"
include "bnj1241.mm"
include "bnj593.mm"
include "bnj937.mm"
include "syl.mm"

theorem bnj1245
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
  let cK: class K
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  assume bnj1245.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1245.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1245.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1245.4: |- D = ( dom g i^i dom h )
  assume bnj1245.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1245.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1245.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )
  assume bnj1245.8: |- Z = <. x , ( h |` _pred ( x , A , R ) ) >.
  assume bnj1245.9: |- K = { h | E. d e. B ( h Fn d /\ A. x e. d ( h ` x ) = ( G ` Z ) ) }

  disjoint A d
  disjoint B f
  disjoint B h
  disjoint f h
  disjoint G f
  disjoint G h
  disjoint Y h
  disjoint Z f
  disjoint d f
  disjoint d h
  disjoint f x
  disjoint h x
  assert |- ( ph -> dom h C_ A )

  proof
    wph
    vh
    cv
    #
    cK
    wcel
    #
    @0
    cdm
    #
    cA
    wss
    #
    wph
    @0
    cC
    cK
    wph
    cA
    cR
    w-bnj15
    vg
    cv
    #
    cC
    wcel
    @0
    cC
    wcel
    @4
    cD
    cres
    @0
    cD
    cres
    wne
    bnj1245.6
    bnj1247
    vx
    cA
    cB
    cC
    cK
    cR
    vf
    vh
    cG
    cY
    cZ
    vd
    bnj1245.2
    bnj1245.3
    bnj1245.8
    bnj1245.9
    bnj1234
    syl6eleq
    @1
    @3
    vd
    @1
    vd
    cv
    #
    cB
    wcel
    #
    @0
    @5
    wfn
    #
    wa
    @3
    vd
    @1
    @7
    vd
    cB
    @1
    @7
    vx
    cv
    #
    @0
    cfv
    cZ
    cG
    cfv
    wceq
    vx
    @5
    wral
    #
    vd
    cB
    @7
    @9
    wa
    vd
    cB
    wrex
    vh
    cK
    bnj1245.9
    abeq2i
    bnj1238
    bnj1196
    @6
    @7
    @5
    cA
    @2
    @6
    @5
    cA
    wss
    #
    cA
    cR
    @8
    c-bnj14
    @5
    wss
    vx
    @5
    wral
    #
    @10
    @11
    wa
    vd
    cB
    bnj1245.1
    abeq2i
    simplbi
    @5
    @0
    fndm
    bnj1241
    bnj593
    bnj937
    syl
end
