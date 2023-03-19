include "cfv.mm"
include "cv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "opeq2d.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "w-bnj15.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "wfn.mm"
include "bnj1436.mm"
include "fndm.mm"
include "anim1i.mm"
include "bnj31.mm"
include "raleq.mm"
include "pm5.32i.mm"
include "rexbii.mm"
include "sylibr.mm"
include "simpr.mm"
include "bnj1265.mm"
include "bnj1234.mm"
include "eleq2s.mm"
include "bnj770.mm"
include "bnj835.mm"
include "bnj1292.mm"
include "bnj1212.mm"
include "bnj1213.mm"
include "bnj1294.mm"
include "bnj771.mm"
include "bnj1293.mm"
include "3eqtr4d.mm"

theorem bnj1296
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
  let cL: class L
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  assume bnj1296.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1296.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1296.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1296.4: |- D = ( dom g i^i dom h )
  assume bnj1296.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1296.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1296.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )
  assume bnj1296.18: |- ( ps -> ( g |` _pred ( x , A , R ) ) = ( h |` _pred ( x , A , R ) ) )
  assume bnj1296.9: |- Z = <. x , ( g |` _pred ( x , A , R ) ) >.
  assume bnj1296.10: |- K = { g | E. d e. B ( g Fn d /\ A. x e. d ( g ` x ) = ( G ` Z ) ) }
  assume bnj1296.11: |- W = <. x , ( h |` _pred ( x , A , R ) ) >.
  assume bnj1296.12: |- L = { h | E. d e. B ( h Fn d /\ A. x e. d ( h ` x ) = ( G ` W ) ) }

  disjoint B f
  disjoint B g
  disjoint f g
  disjoint B h
  disjoint f h
  disjoint D x
  disjoint G d
  disjoint G f
  disjoint G g
  disjoint d f
  disjoint d g
  disjoint G h
  disjoint d h
  disjoint W d
  disjoint W f
  disjoint Y g
  disjoint Y h
  disjoint Z d
  disjoint Z f
  disjoint d x
  disjoint f x
  disjoint g x
  disjoint h x
  assert |- ( ps -> ( g ` x ) = ( h ` x ) )

  proof
    wps
    cZ
    cG
    cfv
    #
    cW
    cG
    cfv
    #
    vx
    cv
    #
    vg
    cv
    #
    cfv
    #
    @2
    vh
    cv
    #
    cfv
    #
    wps
    cZ
    cW
    cG
    wps
    @2
    @3
    cA
    cR
    @2
    c-bnj14
    #
    cres
    #
    cop
    @2
    @5
    @7
    cres
    #
    cop
    cZ
    cW
    wps
    @8
    @9
    @2
    bnj1296.18
    opeq2d
    bnj1296.9
    bnj1296.11
    3eqtr4g
    fveq2d
    wps
    @4
    @0
    wceq
    #
    vx
    @3
    cdm
    #
    wph
    @2
    cE
    wcel
    #
    vy
    cv
    @2
    cR
    wbr
    wn
    vy
    cE
    wral
    #
    @10
    vx
    @11
    wral
    #
    wps
    bnj1296.7
    cA
    cR
    w-bnj15
    #
    @3
    cC
    wcel
    #
    @5
    cC
    wcel
    #
    @3
    cD
    cres
    @5
    cD
    cres
    wne
    #
    @14
    wph
    bnj1296.6
    @14
    @3
    cK
    cC
    @3
    cK
    wcel
    #
    @14
    vd
    cB
    @19
    @11
    vd
    cv
    #
    wceq
    #
    @14
    wa
    #
    @14
    vd
    cB
    @19
    @21
    @10
    vx
    @20
    wral
    #
    wa
    #
    vd
    cB
    wrex
    @22
    vd
    cB
    wrex
    @19
    @3
    @20
    wfn
    #
    @23
    wa
    #
    @24
    vd
    cB
    @26
    vd
    cB
    wrex
    vg
    cK
    bnj1296.10
    bnj1436
    @25
    @21
    @23
    @20
    @3
    fndm
    anim1i
    bnj31
    @22
    @24
    vd
    cB
    @21
    @14
    @23
    @10
    vx
    @11
    @20
    raleq
    pm5.32i
    rexbii
    sylibr
    @21
    @14
    simpr
    bnj31
    bnj1265
    vx
    cA
    cB
    cC
    cK
    cR
    vf
    vg
    cG
    cY
    cZ
    vd
    bnj1296.2
    bnj1296.3
    bnj1296.9
    bnj1296.10
    bnj1234
    eleq2s
    bnj770
    bnj835
    wps
    vx
    cD
    @11
    cD
    @11
    @5
    cdm
    #
    bnj1296.4
    bnj1292
    @4
    @6
    wne
    wph
    wps
    @13
    vx
    cD
    cE
    bnj1296.5
    bnj1296.7
    bnj1212
    #
    bnj1213
    bnj1294
    wps
    @6
    @1
    wceq
    #
    vx
    @27
    wph
    @12
    @13
    @29
    vx
    @27
    wral
    #
    wps
    bnj1296.7
    @15
    @16
    @17
    @18
    @30
    wph
    bnj1296.6
    @30
    @5
    cL
    cC
    @5
    cL
    wcel
    #
    @30
    vd
    cB
    @31
    @27
    @20
    wceq
    #
    @30
    wa
    #
    @30
    vd
    cB
    @31
    @32
    @29
    vx
    @20
    wral
    #
    wa
    #
    vd
    cB
    wrex
    @33
    vd
    cB
    wrex
    @31
    @5
    @20
    wfn
    #
    @34
    wa
    #
    @35
    vd
    cB
    @37
    vd
    cB
    wrex
    vh
    cL
    bnj1296.12
    bnj1436
    @36
    @32
    @34
    @20
    @5
    fndm
    anim1i
    bnj31
    @33
    @35
    vd
    cB
    @32
    @30
    @34
    @29
    vx
    @27
    @20
    raleq
    pm5.32i
    rexbii
    sylibr
    @32
    @30
    simpr
    bnj31
    bnj1265
    vx
    cA
    cB
    cC
    cL
    cR
    vf
    vh
    cG
    cY
    cW
    vd
    bnj1296.2
    bnj1296.3
    bnj1296.11
    bnj1296.12
    bnj1234
    eleq2s
    bnj771
    bnj835
    wps
    vx
    cD
    @27
    cD
    @11
    @27
    bnj1296.4
    bnj1293
    @28
    bnj1213
    bnj1294
    3eqtr4d
end
