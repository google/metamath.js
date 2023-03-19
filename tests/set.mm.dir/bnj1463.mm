include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wsbc.mm"
include "c-bnj14.mm"
include "cres.mm"
include "cop.mm"
include "wex.mm"
include "cvv.mm"
include "elexd.mm"
include "eleq1.mm"
include "fneq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "wss.mm"
include "bnj1317.mm"
include "nfcii.mm"
include "nfel2.mm"
include "bnj1467.mm"
include "nfcv.mm"
include "nffn.mm"
include "bnj1446.mm"
include "nf5i.mm"
include "nfral.mm"
include "nfan.mm"
include "nf5ri.mm"
include "jca32.mm"
include "bnj1465.mm"
include "mpdan.mm"
include "df-rex.mm"
include "sylibr.mm"
include "wb.mm"
include "bnj1466.mm"
include "bnj1448.mm"
include "nfrex.mm"
include "nfeq2.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "opeq2d.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "rexbid.mm"
include "bnj1468.mm"
include "syl.mm"
include "mpbird.mm"
include "fveq2.mm"
include "id.mm"
include "bnj602.mm"
include "reseq2d.mm"
include "opeq12d.mm"
include "syl5eq.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sbcbii.mm"
include "bnj1454.mm"

theorem bnj1463
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
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
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let bnjwtam: wff ta'
  let vw: setvar w
  assume bnj1463.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1463.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1463.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1463.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1463.5: |- D = { x e. A | -. E. f ta }
  assume bnj1463.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1463.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1463.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1463.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1463.10: |- P = U. H
  assume bnj1463.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1463.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1463.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1463.14: |- E = ( { x } u. _trCl ( x , A , R ) )
  assume bnj1463.15: |- ( ch -> Q e. _V )
  assume bnj1463.16: |- ( ch -> A. z e. E ( Q ` z ) = ( G ` W ) )
  assume bnj1463.17: |- ( ch -> Q Fn E )
  assume bnj1463.18: |- ( ch -> E e. B )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint E d
  disjoint E z
  disjoint d z
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint G z
  disjoint f z
  disjoint x z
  disjoint Q z
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint Y z
  disjoint d y
  disjoint x y
  disjoint A w
  disjoint d w
  disjoint f w
  disjoint w x
  disjoint B w
  disjoint C w
  disjoint E w
  disjoint w z
  disjoint G w
  disjoint H w
  disjoint P w
  disjoint Q w
  disjoint R w
  disjoint W w
  disjoint Z w
  assert |- ( ch -> Q e. C )

  proof
    wch
    cQ
    cC
    wcel
    #
    vf
    cv
    #
    vd
    cv
    #
    wfn
    #
    vx
    cv
    #
    @1
    cfv
    #
    cY
    cG
    cfv
    #
    wceq
    #
    vx
    @2
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cQ
    wsbc
    #
    wch
    @3
    vz
    cv
    #
    @1
    cfv
    #
    @12
    @1
    cA
    cR
    @12
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
    vz
    @2
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    vf
    cQ
    wsbc
    #
    @11
    wch
    @22
    cQ
    @2
    wfn
    #
    @12
    cQ
    cfv
    #
    cW
    cG
    cfv
    #
    wceq
    #
    vz
    @2
    wral
    #
    wa
    #
    vd
    cB
    wrex
    #
    wch
    @2
    cB
    wcel
    #
    @28
    wa
    #
    vd
    wex
    #
    @29
    wch
    cE
    cvv
    wcel
    @32
    wch
    cE
    cB
    bnj1463.18
    elexd
    @31
    cE
    cB
    wcel
    #
    cQ
    cE
    wfn
    #
    @26
    vz
    cE
    wral
    #
    wa
    #
    wa
    #
    wch
    vd
    cE
    cvv
    @2
    cE
    wceq
    #
    @30
    @33
    @28
    @36
    @2
    cE
    cB
    eleq1
    @38
    @23
    @34
    @27
    @35
    @2
    cE
    cQ
    fneq2
    @26
    vz
    @2
    cE
    raleq
    anbi12d
    anbi12d
    @37
    vd
    @33
    @36
    vd
    vd
    cE
    cB
    vd
    vw
    cB
    @2
    cA
    wss
    cA
    cR
    @4
    c-bnj14
    #
    @2
    wss
    vx
    @2
    wral
    wa
    vd
    vw
    cB
    bnj1463.1
    bnj1317
    nfcii
    nfel2
    @34
    @35
    vd
    vd
    cE
    cQ
    vd
    vw
    cQ
    wps
    wch
    wta
    vx
    vy
    vw
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
    cY
    cZ
    vd
    bnjwtam
    bnj1463.1
    bnj1463.2
    bnj1463.3
    bnj1463.4
    bnj1463.5
    bnj1463.6
    bnj1463.7
    bnj1463.8
    bnj1463.9
    bnj1463.10
    bnj1463.11
    bnj1463.12
    bnj1467
    nfcii
    #
    vd
    cE
    nfcv
    #
    nffn
    @26
    vd
    vz
    cE
    @41
    @26
    vd
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
    bnj1463.1
    bnj1463.2
    bnj1463.3
    bnj1463.4
    bnj1463.5
    bnj1463.6
    bnj1463.7
    bnj1463.8
    bnj1463.9
    bnj1463.10
    bnj1463.11
    bnj1463.12
    bnj1463.13
    bnj1446
    nf5i
    nfral
    nfan
    nfan
    nf5ri
    wch
    @33
    @34
    @35
    bnj1463.18
    bnj1463.17
    bnj1463.16
    jca32
    bnj1465
    mpdan
    @28
    vd
    cB
    df-rex
    sylibr
    wch
    cQ
    cvv
    wcel
    #
    @22
    @29
    wb
    bnj1463.15
    @21
    @29
    vf
    vw
    cQ
    cvv
    @29
    vf
    @28
    vf
    vd
    cB
    vf
    cB
    nfcv
    @23
    @27
    vf
    vf
    @2
    cQ
    vf
    vw
    cQ
    wps
    wch
    wta
    vx
    vy
    vw
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
    cY
    cZ
    vd
    bnjwtam
    bnj1463.1
    bnj1463.2
    bnj1463.3
    bnj1463.4
    bnj1463.5
    bnj1463.6
    bnj1463.7
    bnj1463.8
    bnj1463.9
    bnj1463.10
    bnj1463.11
    bnj1463.12
    bnj1466
    #
    nfcii
    vf
    @2
    nfcv
    #
    nffn
    @26
    vf
    vz
    @2
    @44
    @26
    vf
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
    bnj1463.1
    bnj1463.2
    bnj1463.3
    bnj1463.4
    bnj1463.5
    bnj1463.6
    bnj1463.7
    bnj1463.8
    bnj1463.9
    bnj1463.10
    bnj1463.11
    bnj1463.12
    bnj1463.13
    bnj1448
    nf5i
    nfral
    nfan
    nfrex
    nf5ri
    @1
    cQ
    wceq
    #
    @20
    @28
    vd
    cB
    vd
    @1
    cQ
    @40
    nfeq2
    @45
    @3
    @23
    @19
    @27
    @2
    @1
    cQ
    fneq1
    @45
    @18
    @26
    vz
    @2
    @45
    @13
    @24
    @17
    @25
    @12
    @1
    cQ
    fveq1
    @45
    @16
    cW
    cG
    @45
    @16
    @12
    cQ
    @14
    cres
    #
    cop
    cW
    @45
    @15
    @46
    @12
    @1
    cQ
    @14
    reseq1
    opeq2d
    bnj1463.13
    syl6eqr
    fveq2d
    eqeq12d
    ralbidv
    anbi12d
    rexbid
    @43
    bnj1468
    syl
    mpbird
    @10
    @21
    vf
    cQ
    @9
    @20
    vd
    cB
    @8
    @19
    @3
    @7
    @18
    vx
    vz
    @2
    @4
    @12
    wceq
    #
    @5
    @13
    @6
    @17
    @4
    @12
    @1
    fveq2
    @47
    cY
    @16
    cG
    @47
    cY
    @4
    @1
    @39
    cres
    #
    cop
    @16
    bnj1463.2
    @47
    @4
    @12
    @48
    @15
    @47
    id
    @47
    @39
    @14
    @1
    cA
    cR
    @4
    @12
    bnj602
    reseq2d
    opeq12d
    syl5eq
    fveq2d
    eqeq12d
    cbvralv
    anbi2i
    rexbii
    sbcbii
    sylibr
    wch
    @42
    @0
    @11
    wb
    bnj1463.15
    @10
    vf
    cC
    cQ
    bnj1463.3
    bnj1454
    syl
    mpbird
end
