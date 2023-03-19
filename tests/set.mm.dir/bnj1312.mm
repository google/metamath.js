include "w-bnj15.mm"
include "wex.mm"
include "wral.mm"
include "cv.mm"
include "cdm.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "wceq.mm"
include "wrex.mm"
include "c0.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "wss.mm"
include "wne.mm"
include "simplbi.mm"
include "ssrab3.mm"
include "a1i.mm"
include "simprbi.mm"
include "bnj1230.mm"
include "bnj1228.mm"
include "syl3anc.mm"
include "wa.mm"
include "nfv.mm"
include "nfcii.mm"
include "nfcv.mm"
include "nfne.mm"
include "nfan.mm"
include "nfxfr.mm"
include "nf5ri.mm"
include "bnj1521.mm"
include "simp2bi.mm"
include "bnj1538.mm"
include "cvv.mm"
include "bnj1489.mm"
include "wfun.mm"
include "bnj835.mm"
include "bnj1384.mm"
include "syl.mm"
include "bnj1415.mm"
include "bnj1422.mm"
include "bnj1416.mm"
include "bnj1421.mm"
include "bnj1423.mm"
include "wfn.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "bnj1452.mm"
include "bnj1463.mm"
include "jca.mm"
include "bnj1491.mm"
include "mpdan.mm"
include "bnj1198.mm"
include "nsyl3.mm"
include "bnj1304.mm"
include "bnj1541.mm"
include "bnj1476.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "sylib.mm"

theorem bnj1312
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
  assume bnj1312.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1312.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1312.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1312.4: |- ( ta <-> ( f e. C /\ dom f = ( { x } u. _trCl ( x , A , R ) ) ) )
  assume bnj1312.5: |- D = { x e. A | -. E. f ta }
  assume bnj1312.6: |- ( ps <-> ( R _FrSe A /\ D =/= (/) ) )
  assume bnj1312.7: |- ( ch <-> ( ps /\ x e. D /\ A. y e. D -. y R x ) )
  assume bnj1312.8: |- ( ta' <-> [. y / x ]. ta )
  assume bnj1312.9: |- H = { f | E. y e. _pred ( x , A , R ) ta' }
  assume bnj1312.10: |- P = U. H
  assume bnj1312.11: |- Z = <. x , ( P |` _pred ( x , A , R ) ) >.
  assume bnj1312.12: |- Q = ( P u. { <. x , ( G ` Z ) >. } )
  assume bnj1312.13: |- W = <. z , ( Q |` _pred ( z , A , R ) ) >.
  assume bnj1312.14: |- E = ( { x } u. _trCl ( x , A , R ) )

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
  disjoint C y
  disjoint D y
  disjoint E d
  disjoint E f
  disjoint E y
  disjoint E z
  disjoint G d
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint Q z
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y z
  disjoint ch z
  disjoint ps y
  disjoint ta y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint D w
  disjoint R w
  assert |- ( R _FrSe A -> A. x e. A E. f e. C dom f = ( { x } u. _trCl ( x , A , R ) ) )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    vf
    wex
    #
    vx
    cA
    wral
    vf
    cv
    #
    cdm
    vx
    cv
    #
    csn
    cA
    cR
    @3
    c-bnj18
    #
    cun
    #
    wceq
    #
    vf
    cC
    wrex
    #
    vx
    cA
    wral
    @1
    @0
    vx
    cA
    cD
    bnj1312.5
    wps
    @0
    cD
    c0
    bnj1312.6
    wps
    wch
    @3
    cD
    wcel
    #
    vx
    vy
    cv
    @3
    cR
    wbr
    wn
    vy
    cD
    wral
    #
    wps
    wch
    vx
    cD
    wps
    @0
    cD
    cA
    wss
    #
    cD
    c0
    wne
    #
    @9
    vx
    cD
    wrex
    wps
    @0
    @11
    bnj1312.6
    simplbi
    #
    @10
    wps
    @1
    wn
    #
    vx
    cA
    cD
    bnj1312.5
    ssrab3
    a1i
    wps
    @0
    @11
    bnj1312.6
    simprbi
    vx
    vy
    vw
    cA
    cD
    cR
    @13
    vx
    vw
    cA
    cD
    bnj1312.5
    bnj1230
    #
    bnj1228
    syl3anc
    bnj1312.7
    wps
    vx
    wps
    @0
    @11
    wa
    vx
    bnj1312.6
    @0
    @11
    vx
    @0
    vx
    nfv
    vx
    cD
    c0
    vx
    vw
    cD
    @14
    nfcii
    vx
    c0
    nfcv
    nfne
    nfan
    nfxfr
    nf5ri
    bnj1521
    wch
    wps
    @8
    @9
    bnj1312.7
    simp2bi
    @8
    @1
    wch
    @13
    vx
    cD
    cA
    bnj1312.5
    bnj1538
    wch
    @2
    cC
    wcel
    @6
    wa
    #
    vf
    wta
    wch
    cQ
    cvv
    wcel
    @15
    vf
    wex
    #
    wps
    wch
    wta
    vx
    vy
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
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    bnj1489
    #
    wps
    wch
    wta
    vx
    vy
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
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    wch
    cQ
    cC
    wcel
    cQ
    cdm
    @5
    wceq
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
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    bnj1312.13
    bnj1312.14
    @17
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
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    bnj1312.13
    bnj1312.14
    wch
    cP
    @4
    wch
    @0
    cP
    wfun
    wps
    @8
    @9
    @0
    wch
    bnj1312.7
    @12
    bnj835
    wps
    wch
    wta
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cR
    vf
    cG
    cH
    cY
    vd
    bnjwtam
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1384
    syl
    #
    wps
    wch
    wta
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cR
    vf
    cG
    cH
    cY
    vd
    bnjwtam
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1415
    #
    bnj1422
    wch
    cQ
    @5
    wps
    wch
    wta
    vx
    vy
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
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    @18
    wps
    wch
    wta
    vx
    vy
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
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    @19
    bnj1416
    #
    @19
    bnj1421
    @20
    bnj1422
    #
    bnj1423
    wch
    cQ
    @5
    wfn
    cQ
    cE
    wfn
    @21
    cE
    @5
    cQ
    bnj1312.14
    fneq2i
    sylibr
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
    cE
    cG
    cH
    cW
    cY
    cZ
    vd
    bnjwtam
    bnj1312.1
    bnj1312.2
    bnj1312.3
    bnj1312.4
    bnj1312.5
    bnj1312.6
    bnj1312.7
    bnj1312.8
    bnj1312.9
    bnj1312.10
    bnj1312.11
    bnj1312.12
    bnj1312.13
    bnj1312.14
    bnj1452
    bnj1463
    @20
    jca
    bnj1491
    mpdan
    bnj1312.4
    bnj1198
    nsyl3
    bnj1304
    bnj1541
    bnj1476
    @1
    @7
    vx
    cA
    @1
    @16
    @7
    wta
    @15
    vf
    bnj1312.4
    exbii
    @6
    vf
    cC
    df-rex
    bitr4i
    ralbii
    sylib
end
