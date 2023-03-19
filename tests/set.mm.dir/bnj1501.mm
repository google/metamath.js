include "w-bnj15.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "ciun.mm"
include "simprbi.mm"
include "wfn.mm"
include "bnj60.mm"
include "fndm.mm"
include "syl.mm"
include "bnj832.mm"
include "eleqtrrd.mm"
include "cuni.mm"
include "dmeqi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "bnj1317.mm"
include "bnj1400.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "bnj1405.mm"
include "bnj1209.mm"
include "bnj1436.mm"
include "bnj1299.mm"
include "bnj31.mm"
include "bnj836.mm"
include "bnj1518.mm"
include "bnj1521.mm"
include "wfun.mm"
include "bnj930.mm"
include "bnj835.mm"
include "wss.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "simp3bi.mm"
include "bnj1502.mm"
include "bnj1514.mm"
include "bnj1294.mm"
include "eqtrd.mm"
include "bnj1517.mm"
include "eleqtrd.mm"
include "sseqtr4d.mm"
include "bnj1503.mm"
include "opeq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "bnj593.mm"
include "bnj1519.mm"
include "bnj1397.mm"
include "bnj1520.mm"
include "bnj1459.mm"

theorem bnj1501
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
  let vw: setvar w
  assume bnj1501.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1501.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1501.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1501.4: |- F = U. C
  assume bnj1501.5: |- ( ph <-> ( R _FrSe A /\ x e. A ) )
  assume bnj1501.6: |- ( ps <-> ( ph /\ f e. C /\ x e. dom f ) )
  assume bnj1501.7: |- ( ch <-> ( ps /\ d e. B /\ dom f = d ) )

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
  disjoint Y d
  disjoint d ph
  disjoint f ph
  disjoint C w
  disjoint f w
  assert |- ( R _FrSe A -> A. x e. A ( F ` x ) = ( G ` <. x , ( F |` _pred ( x , A , R ) ) >. ) )

  proof
    cA
    cR
    w-bnj15
    #
    wph
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cF
    cA
    cR
    @1
    c-bnj14
    #
    cres
    #
    cop
    #
    cG
    cfv
    #
    wceq
    #
    vx
    cA
    bnj1501.5
    wph
    @7
    vf
    wph
    wps
    @7
    vf
    @1
    vf
    cv
    #
    cdm
    #
    wcel
    #
    wph
    wps
    vf
    cC
    wph
    vf
    cC
    @9
    @1
    wph
    @1
    cF
    cdm
    #
    vf
    cC
    @9
    ciun
    #
    wph
    @1
    cA
    @11
    wph
    @0
    @1
    cA
    wcel
    #
    bnj1501.5
    simprbi
    @0
    @13
    @11
    cA
    wceq
    #
    wph
    bnj1501.5
    @0
    cF
    cA
    wfn
    @14
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
    bnj1501.1
    bnj1501.2
    bnj1501.3
    bnj1501.4
    bnj60
    #
    cA
    cF
    fndm
    syl
    bnj832
    eleqtrrd
    @11
    cC
    cuni
    #
    cdm
    @12
    cF
    @16
    bnj1501.4
    dmeqi
    vf
    vw
    cC
    @8
    vd
    cv
    #
    wfn
    #
    @1
    @8
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    vx
    @17
    wral
    #
    wa
    vd
    cB
    wrex
    #
    vf
    vw
    cC
    bnj1501.3
    bnj1317
    bnj1400
    eqtri
    syl6eleq
    bnj1405
    bnj1501.6
    bnj1209
    wps
    @7
    vd
    wps
    wch
    @7
    vd
    @9
    @17
    wceq
    #
    wps
    wch
    vd
    cB
    wph
    @8
    cC
    wcel
    #
    @10
    @24
    vd
    cB
    wrex
    wps
    bnj1501.6
    @25
    @18
    @24
    vd
    cB
    @25
    @18
    @22
    vd
    cB
    @23
    vf
    cC
    bnj1501.3
    bnj1436
    bnj1299
    @17
    @8
    fndm
    bnj31
    bnj836
    bnj1501.7
    wph
    wps
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
    bnj1501.1
    bnj1501.2
    bnj1501.3
    bnj1501.4
    bnj1501.5
    bnj1501.6
    bnj1518
    bnj1521
    wch
    @2
    @20
    @6
    wps
    @17
    cB
    wcel
    #
    @24
    @2
    @20
    wceq
    wch
    bnj1501.7
    wps
    @2
    @19
    @20
    wps
    @1
    cF
    @8
    wph
    @25
    @10
    cF
    wfun
    #
    wps
    bnj1501.6
    @0
    @13
    @27
    wph
    bnj1501.5
    @0
    cA
    cF
    @15
    bnj930
    bnj832
    bnj835
    #
    wph
    @25
    @10
    @8
    cF
    wss
    #
    wps
    bnj1501.6
    @25
    @8
    @16
    cF
    @8
    cC
    elssuni
    bnj1501.4
    syl6sseqr
    bnj836
    #
    wps
    wph
    @25
    @10
    bnj1501.6
    simp3bi
    #
    bnj1502
    wps
    @21
    vx
    @9
    wph
    @25
    @10
    @21
    vx
    @9
    wral
    wps
    bnj1501.6
    vx
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnj1501.1
    bnj1501.2
    bnj1501.3
    bnj1514
    bnj836
    @31
    bnj1294
    eqtrd
    bnj835
    wch
    @5
    cY
    cG
    wch
    @5
    @1
    @8
    @3
    cres
    #
    cop
    cY
    wch
    @4
    @32
    @1
    wch
    @3
    cF
    @8
    wps
    @26
    @24
    @27
    wch
    bnj1501.7
    @28
    bnj835
    wps
    @26
    @24
    @29
    wch
    bnj1501.7
    @30
    bnj835
    wch
    @3
    @17
    @9
    wch
    @3
    @17
    wss
    #
    vx
    @17
    wps
    @26
    @24
    @33
    vx
    @17
    wral
    #
    wch
    bnj1501.7
    @17
    cA
    wss
    @34
    vd
    cB
    bnj1501.1
    bnj1517
    bnj836
    wch
    @1
    @9
    @17
    wps
    @26
    @24
    @10
    wch
    bnj1501.7
    @31
    bnj835
    wch
    wps
    @26
    @24
    bnj1501.7
    simp3bi
    #
    eleqtrd
    bnj1294
    @35
    sseqtr4d
    bnj1503
    opeq2d
    bnj1501.2
    syl6eqr
    fveq2d
    eqtr4d
    bnj593
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
    bnj1501.1
    bnj1501.2
    bnj1501.3
    bnj1501.4
    bnj1519
    bnj1397
    bnj593
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
    bnj1501.1
    bnj1501.2
    bnj1501.3
    bnj1501.4
    bnj1520
    bnj1397
    bnj1459
end
