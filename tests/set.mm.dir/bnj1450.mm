include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "wcel.mm"
include "cuni.mm"
include "ciun.mm"
include "c-bnj18.mm"
include "simprbi.mm"
include "wfn.mm"
include "fndm.mm"
include "syl.mm"
include "bnj832.mm"
include "eleqtrrd.mm"
include "dmeqi.mm"
include "syl6eleq.mm"
include "c-bnj14.mm"
include "wrex.mm"
include "bnj1317.mm"
include "bnj1400.mm"
include "bnj1405.mm"
include "bnj1449.mm"
include "bnj1521.mm"
include "csn.mm"
include "cun.mm"
include "w3a.mm"
include "wa.mm"
include "bnj1436.mm"
include "bnj836.mm"
include "bnj1373.mm"
include "rexbii.mm"
include "sylib.mm"
include "bnj1196.mm"
include "3anass.mm"
include "bnj1198.mm"
include "w-bnj17.mm"
include "bnj252.mm"
include "bitri.mm"
include "bnj1444.mm"
include "bnj1340.mm"
include "wral.mm"
include "bnj771.mm"
include "bnj1445.mm"
include "bnj1254.mm"
include "fveq2.mm"
include "cres.mm"
include "cop.mm"
include "id.mm"
include "bnj602.mm"
include "reseq2d.mm"
include "opeq12d.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "simp3bi.mm"
include "bnj769.mm"
include "eleqtrd.mm"
include "bnj1294.mm"
include "wfun.mm"
include "bnj930.mm"
include "bnj835.mm"
include "wss.mm"
include "simp2bi.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ssun3.mm"
include "3syl.mm"
include "bnj1502.mm"
include "bnj1517.mm"
include "bnj770.mm"
include "sseq1d.mm"
include "sseqtr4d.mm"
include "bnj1503.mm"
include "opeq2d.mm"
include "3eqtr4d.mm"
include "bnj593.mm"
include "bnj1446.mm"
include "bnj1397.mm"
include "bnj1447.mm"
include "bnj1448.mm"

theorem bnj1450
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  let vw: setvar w
  assume bnj1450.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1450.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1450.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1450.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1450.5: |- D = { x e. A | -. E. f ta }
  assume bnj1450.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1450.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1450.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1450.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1450.10: |- P = U. H
  assume bnj1450.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1450.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1450.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1450.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1450.15: |- ( ch -> P Fn _trCl ( x , A , R ) )
  assume bnj1450.16: |- ( ch -> Q Fn ( { x } u. _trCl ( x , A , R ) ) )
  assume bnj1450.17: |- ( th <-> ( ch /\ z e. E ) )
  assume bnj1450.18: |- ( et <-> ( th /\ z e. { x } ) )
  assume bnj1450.19: |- ( ze <-> ( th /\ z e. _trCl ( x , A , R ) ) )
  assume bnj1450.20: |- ( rh <-> ( ze /\ f e. H /\ z e. dom f ) )
  assume bnj1450.21: |- ( si <-> ( rh /\ y e. _pred ( x , A , R ) /\ f e. C /\ dom f = ( { y } u. _trCl ( y , A , R ) ) ) )
  assume bnj1450.22: |- ( ph <-> ( si /\ d e. B /\ f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) )
  assume bnj1450.23: |- X = <. z , ( f |` _pred ( z , A , R ) ) >.

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B f
  disjoint D y
  disjoint E d
  disjoint E f
  disjoint E y
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X x
  disjoint Y z
  disjoint ps y
  disjoint H w
  disjoint f w
  assert |- ( ze -> ( Q ` z ) = ( G ` W ) )

  proof
    wze
    vz
    cv
    #
    cQ
    cfv
    #
    cW
    cG
    cfv
    #
    wceq
    #
    vf
    wze
    wrh
    @3
    vf
    @0
    vf
    cv
    #
    cdm
    #
    wcel
    #
    wze
    wrh
    vf
    cH
    wze
    vf
    cH
    @5
    @0
    wze
    @0
    cH
    cuni
    #
    cdm
    #
    vf
    cH
    @5
    ciun
    wze
    @0
    cP
    cdm
    #
    @8
    wze
    @0
    cA
    cR
    vx
    cv
    #
    c-bnj18
    #
    @9
    wze
    wth
    @0
    @11
    wcel
    #
    bnj1450.19
    simprbi
    wth
    @12
    @9
    @11
    wceq
    #
    wze
    bnj1450.19
    wch
    @0
    cE
    wcel
    #
    @13
    wth
    bnj1450.17
    wch
    cP
    @11
    wfn
    @13
    bnj1450.15
    @11
    cP
    fndm
    syl
    bnj832
    bnj832
    eleqtrrd
    cP
    @7
    bnj1450.10
    dmeqi
    syl6eleq
    vf
    vw
    cH
    bnjwtam
    vy
    cA
    cR
    @10
    c-bnj14
    #
    wrex
    #
    vf
    vw
    cH
    bnj1450.9
    bnj1317
    bnj1400
    syl6eleq
    bnj1405
    bnj1450.20
    wps
    wch
    wth
    wta
    wet
    wze
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1450.14
    bnj1450.15
    bnj1450.16
    bnj1450.17
    bnj1450.18
    bnj1450.19
    bnj1449
    bnj1521
    wrh
    @3
    vy
    wrh
    wsi
    @3
    vy
    wrh
    wsi
    vy
    cv
    #
    @15
    wcel
    #
    @4
    cC
    wcel
    #
    @5
    @17
    csn
    cA
    cR
    @17
    c-bnj18
    cun
    wceq
    #
    w3a
    #
    vy
    wrh
    @18
    @19
    @20
    wa
    #
    wa
    vy
    @21
    wrh
    @22
    vy
    @15
    wrh
    @16
    @22
    vy
    @15
    wrex
    wze
    @4
    cH
    wcel
    #
    @6
    @16
    wrh
    bnj1450.20
    @16
    vf
    cH
    bnj1450.9
    bnj1436
    bnj836
    bnjwtam
    @22
    vy
    @15
    wta
    vx
    vy
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.8
    bnj1373
    rexbii
    sylib
    bnj1196
    @18
    @19
    @20
    3anass
    bnj1198
    wsi
    wrh
    @18
    @19
    @20
    w-bnj17
    wrh
    @21
    wa
    bnj1450.21
    wrh
    @18
    @19
    @20
    bnj252
    bitri
    wps
    wch
    wth
    wta
    wet
    wze
    wrh
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1450.14
    bnj1450.15
    bnj1450.16
    bnj1450.17
    bnj1450.18
    bnj1450.19
    bnj1450.20
    bnj1444
    bnj1340
    wsi
    @3
    vd
    wsi
    wph
    @3
    vd
    wsi
    wph
    vd
    cv
    #
    cB
    wcel
    #
    @4
    @24
    wfn
    #
    @10
    @4
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    vx
    @24
    wral
    #
    w3a
    #
    vd
    wsi
    @25
    @26
    @30
    wa
    #
    wa
    vd
    @31
    wsi
    @32
    vd
    cB
    wrh
    @18
    @19
    @20
    @32
    vd
    cB
    wrex
    #
    wsi
    bnj1450.21
    @33
    vf
    cC
    bnj1450.3
    bnj1436
    bnj771
    bnj1196
    @25
    @26
    @30
    3anass
    bnj1198
    wph
    wsi
    @25
    @26
    @30
    w-bnj17
    wsi
    @31
    wa
    bnj1450.22
    wsi
    @25
    @26
    @30
    bnj252
    bitri
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cE
    cG
    cH
    cW
    cX
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1450.14
    bnj1450.15
    bnj1450.16
    bnj1450.17
    bnj1450.18
    bnj1450.19
    bnj1450.20
    bnj1450.21
    bnj1450.22
    bnj1450.23
    bnj1445
    bnj1340
    wph
    @0
    @4
    cfv
    #
    cX
    cG
    cfv
    #
    @1
    @2
    wph
    @34
    @35
    wceq
    #
    vz
    @24
    wph
    @30
    @36
    vz
    @24
    wral
    wph
    wsi
    @25
    @26
    @30
    bnj1450.22
    bnj1254
    @29
    @36
    vx
    vz
    @24
    @10
    @0
    wceq
    #
    @27
    @34
    @28
    @35
    @10
    @0
    @4
    fveq2
    @37
    cY
    cX
    cG
    @37
    @10
    @4
    @15
    cres
    #
    cop
    @0
    @4
    cA
    cR
    @0
    c-bnj14
    #
    cres
    #
    cop
    #
    cY
    cX
    @37
    @10
    @0
    @38
    @40
    @37
    id
    @37
    @15
    @39
    @4
    cA
    cR
    @10
    @0
    bnj602
    #
    reseq2d
    opeq12d
    bnj1450.2
    bnj1450.23
    3eqtr4g
    fveq2d
    eqeq12d
    cbvralv
    sylib
    wph
    @0
    @5
    @24
    wsi
    @25
    @26
    @30
    @6
    wph
    bnj1450.22
    wrh
    @18
    @19
    @20
    @6
    wsi
    bnj1450.21
    wrh
    wze
    @23
    @6
    bnj1450.20
    simp3bi
    bnj769
    bnj769
    #
    wsi
    @25
    @26
    @30
    @5
    @24
    wceq
    wph
    bnj1450.22
    @24
    @4
    fndm
    bnj771
    #
    eleqtrd
    #
    bnj1294
    wph
    @0
    cQ
    @4
    wsi
    @25
    @26
    @30
    cQ
    wfun
    #
    wph
    bnj1450.22
    wrh
    @18
    @19
    @20
    @46
    wsi
    bnj1450.21
    wze
    @23
    @6
    @46
    wrh
    bnj1450.20
    wth
    @12
    @46
    wze
    bnj1450.19
    wch
    @14
    @46
    wth
    bnj1450.17
    wch
    @10
    csn
    @11
    cun
    cQ
    bnj1450.16
    bnj930
    bnj832
    bnj832
    bnj835
    bnj769
    bnj769
    #
    wph
    @23
    @4
    cP
    wss
    #
    @4
    cQ
    wss
    wsi
    @25
    @26
    @30
    @23
    wph
    bnj1450.22
    wrh
    @18
    @19
    @20
    @23
    wsi
    bnj1450.21
    wrh
    wze
    @23
    @6
    bnj1450.20
    simp2bi
    bnj769
    bnj769
    @23
    @4
    @7
    cP
    @4
    cH
    elssuni
    bnj1450.10
    syl6sseqr
    @48
    @4
    cP
    @10
    cZ
    cG
    cfv
    cop
    csn
    #
    cun
    cQ
    @4
    cP
    @49
    ssun3
    bnj1450.12
    syl6sseqr
    3syl
    #
    @43
    bnj1502
    wph
    cW
    cX
    cG
    wph
    @0
    cQ
    @39
    cres
    #
    cop
    @41
    cW
    cX
    wph
    @51
    @40
    @0
    wph
    @39
    cQ
    @4
    @47
    @50
    wph
    @39
    @24
    @5
    wph
    @39
    @24
    wss
    #
    vz
    @24
    wph
    @15
    @24
    wss
    #
    vx
    @24
    wral
    #
    @52
    vz
    @24
    wral
    wsi
    @25
    @26
    @30
    @54
    wph
    bnj1450.22
    @24
    cA
    wss
    @54
    vd
    cB
    bnj1450.1
    bnj1517
    bnj770
    @53
    @52
    vx
    vz
    @24
    @37
    @15
    @39
    @24
    @42
    sseq1d
    cbvralv
    sylib
    @45
    bnj1294
    @44
    sseqtr4d
    bnj1503
    opeq2d
    bnj1450.13
    bnj1450.23
    3eqtr4g
    fveq2d
    3eqtr4d
    bnj593
    wps
    wch
    wta
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1446
    bnj1397
    bnj593
    wps
    wch
    wta
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1447
    bnj1397
    bnj593
    wps
    wch
    wta
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    vf
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1450.1
    bnj1450.2
    bnj1450.3
    bnj1450.4
    bnj1450.5
    bnj1450.6
    bnj1450.7
    bnj1450.8
    bnj1450.9
    bnj1450.10
    bnj1450.11
    bnj1450.12
    bnj1450.13
    bnj1448
    bnj1397
end
