include "cv.mm"
include "c-bnj14.mm"
include "cdm.mm"
include "cin.mm"
include "wss.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wfn.mm"
include "wa.mm"
include "bnj1256.mm"
include "bnj1196.mm"
include "bnj1517.mm"
include "adantr.mm"
include "wb.mm"
include "wceq.mm"
include "fndm.mm"
include "sseq2.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "adantl.mm"
include "mpbird.mm"
include "bnj593.mm"
include "bnj937.mm"
include "bnj835.mm"
include "cfv.mm"
include "wne.mm"
include "ssrab3.mm"
include "bnj1292.mm"
include "sstri.mm"
include "sseli.mm"
include "bnj836.mm"
include "bnj1294.mm"
include "bnj1259.mm"
include "bnj1293.mm"
include "ssind.mm"
include "syl6sseqr.mm"

theorem bnj1286
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
  assume bnj1286.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1286.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1286.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1286.4: |- D = ( dom g i^i dom h )
  assume bnj1286.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1286.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1286.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )

  disjoint A d
  disjoint A f
  disjoint d f
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint B h
  disjoint f h
  disjoint D x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint R d
  disjoint R f
  disjoint Y g
  disjoint Y h
  disjoint d g
  disjoint d x
  disjoint f x
  disjoint g x
  disjoint d h
  disjoint h x
  assert |- ( ps -> _pred ( x , A , R ) C_ D )

  proof
    wps
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    vg
    cv
    #
    cdm
    #
    vh
    cv
    #
    cdm
    #
    cin
    cD
    wps
    @1
    @3
    @5
    wps
    @1
    @3
    wss
    #
    vx
    @3
    wph
    @0
    cE
    wcel
    #
    vy
    cv
    @0
    cR
    wbr
    wn
    vy
    cE
    wral
    #
    @6
    vx
    @3
    wral
    #
    wps
    bnj1286.7
    wph
    @9
    vd
    wph
    vd
    cv
    #
    cB
    wcel
    #
    @2
    @10
    wfn
    #
    wa
    #
    @9
    vd
    wph
    @12
    vd
    cB
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    vf
    vg
    vh
    cE
    cG
    cY
    vd
    bnj1286.1
    bnj1286.2
    bnj1286.3
    bnj1286.4
    bnj1286.5
    bnj1286.6
    bnj1286.7
    bnj1256
    bnj1196
    @13
    @9
    @1
    @10
    wss
    #
    vx
    @10
    wral
    #
    @11
    @15
    @12
    @10
    cA
    wss
    @15
    vd
    cB
    bnj1286.1
    bnj1517
    #
    adantr
    @12
    @9
    @15
    wb
    #
    @11
    @12
    @3
    @10
    wceq
    @17
    @10
    @2
    fndm
    @6
    @14
    vx
    @3
    @10
    @3
    @10
    @1
    sseq2
    raleqbi1dv
    syl
    adantl
    mpbird
    bnj593
    bnj937
    bnj835
    wph
    @7
    @8
    @0
    @3
    wcel
    wps
    bnj1286.7
    cE
    @3
    @0
    cE
    cD
    @3
    @0
    @2
    cfv
    @0
    @4
    cfv
    wne
    vx
    cD
    cE
    bnj1286.5
    ssrab3
    #
    cD
    @3
    @5
    bnj1286.4
    bnj1292
    sstri
    sseli
    bnj836
    bnj1294
    wps
    @1
    @5
    wss
    #
    vx
    @5
    wph
    @7
    @8
    @19
    vx
    @5
    wral
    #
    wps
    bnj1286.7
    wph
    @20
    vd
    wph
    @11
    @4
    @10
    wfn
    #
    wa
    #
    @20
    vd
    wph
    @21
    vd
    cB
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    vf
    vg
    vh
    cE
    cG
    cY
    vd
    bnj1286.1
    bnj1286.2
    bnj1286.3
    bnj1286.4
    bnj1286.5
    bnj1286.6
    bnj1286.7
    bnj1259
    bnj1196
    @22
    @20
    @15
    @11
    @15
    @21
    @16
    adantr
    @21
    @20
    @15
    wb
    #
    @11
    @21
    @5
    @10
    wceq
    @23
    @10
    @4
    fndm
    @19
    @14
    vx
    @5
    @10
    @5
    @10
    @1
    sseq2
    raleqbi1dv
    syl
    adantl
    mpbird
    bnj593
    bnj937
    bnj835
    wph
    @7
    @8
    @0
    @5
    wcel
    wps
    bnj1286.7
    cE
    @5
    @0
    cE
    cD
    @5
    @18
    cD
    @3
    @5
    bnj1286.4
    bnj1293
    sstri
    sseli
    bnj836
    bnj1294
    ssind
    bnj1286.4
    syl6sseqr
end
