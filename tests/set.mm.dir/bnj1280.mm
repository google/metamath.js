include "cv.mm"
include "c-bnj14.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "bnj1286.mm"
include "sseld.mm"
include "wn.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "wal.mm"
include "disj1.mm"
include "sylib.mm"
include "19.21bi.mm"
include "wne.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "elrab2.mm"
include "notbii.mm"
include "imnan.mm"
include "nne.mm"
include "imbi2i.mm"
include "3bitr2i.mm"
include "syl6ib.mm"
include "mpdd.mm"
include "imp.mm"
include "fvres.mm"
include "syl6.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "resabs1d.mm"
include "eqeq12d.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "wbr.mm"
include "bnj1256.mm"
include "cdm.mm"
include "bnj1292.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "fnssres.mm"
include "mpdan.mm"
include "bnj31.mm"
include "bnj1265.mm"
include "bnj835.mm"
include "bnj1259.mm"
include "bnj1293.mm"
include "fvreseq.mm"
include "syl21anc.mm"
include "bitr3d.mm"
include "mpbird.mm"

theorem bnj1280
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
  let vz: setvar z
  assume bnj1280.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1280.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1280.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1280.4: |- D = ( dom g i^i dom h )
  assume bnj1280.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1280.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1280.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )
  assume bnj1280.17: |- ( ps -> ( _pred ( x , A , R ) i^i E ) = (/) )

  disjoint A d
  disjoint A f
  disjoint d f
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint B h
  disjoint f h
  disjoint D d
  disjoint D x
  disjoint d x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint R d
  disjoint R f
  disjoint Y g
  disjoint Y h
  disjoint d g
  disjoint f x
  disjoint g x
  disjoint d h
  disjoint h x
  disjoint A z
  disjoint D z
  disjoint x z
  disjoint E z
  disjoint R z
  disjoint g z
  disjoint h z
  disjoint ps z
  assert |- ( ps -> ( g |` _pred ( x , A , R ) ) = ( h |` _pred ( x , A , R ) ) )

  proof
    wps
    vg
    cv
    #
    cA
    cR
    vx
    cv
    #
    c-bnj14
    #
    cres
    #
    vh
    cv
    #
    @2
    cres
    #
    wceq
    #
    vz
    cv
    #
    @0
    cD
    cres
    #
    cfv
    #
    @7
    @4
    cD
    cres
    #
    cfv
    #
    wceq
    #
    vz
    @2
    wral
    #
    wps
    @12
    vz
    @2
    wps
    @7
    @2
    wcel
    #
    wa
    @7
    @0
    cfv
    #
    @7
    @4
    cfv
    #
    @9
    @11
    wps
    @14
    @15
    @16
    wceq
    #
    wps
    @14
    @7
    cD
    wcel
    #
    @17
    wps
    @2
    cD
    @7
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
    bnj1280.1
    bnj1280.2
    bnj1280.3
    bnj1280.4
    bnj1280.5
    bnj1280.6
    bnj1280.7
    bnj1286
    #
    sseld
    #
    wps
    @14
    @7
    cE
    wcel
    #
    wn
    #
    @18
    @17
    wi
    #
    wps
    @14
    @22
    wi
    #
    vz
    wps
    @2
    cE
    cin
    c0
    wceq
    @24
    vz
    wal
    bnj1280.17
    vz
    @2
    cE
    disj1
    sylib
    19.21bi
    @22
    @18
    @15
    @16
    wne
    #
    wa
    #
    wn
    @18
    @25
    wn
    #
    wi
    @23
    @21
    @26
    @1
    @0
    cfv
    #
    @1
    @4
    cfv
    #
    wne
    @25
    vx
    @7
    cD
    cE
    @1
    @7
    wceq
    @28
    @15
    @29
    @16
    @1
    @7
    @0
    fveq2
    @1
    @7
    @4
    fveq2
    neeq12d
    bnj1280.5
    elrab2
    notbii
    @18
    @25
    imnan
    @27
    @17
    @18
    @15
    @16
    nne
    imbi2i
    3bitr2i
    syl6ib
    mpdd
    imp
    wps
    @14
    @9
    @15
    wceq
    #
    wps
    @14
    @18
    @30
    @20
    @7
    cD
    @0
    fvres
    syl6
    imp
    wps
    @14
    @11
    @16
    wceq
    #
    wps
    @14
    @18
    @31
    @20
    @7
    cD
    @4
    fvres
    syl6
    imp
    3eqtr4d
    ralrimiva
    wps
    @8
    @2
    cres
    #
    @10
    @2
    cres
    #
    wceq
    #
    @6
    @13
    wps
    @32
    @3
    @33
    @5
    wps
    @0
    @2
    cD
    @19
    resabs1d
    wps
    @4
    @2
    cD
    @19
    resabs1d
    eqeq12d
    wps
    @8
    cD
    wfn
    #
    @10
    cD
    wfn
    #
    @2
    cD
    wss
    @34
    @13
    wb
    wph
    @1
    cE
    wcel
    #
    vy
    cv
    @1
    cR
    wbr
    wn
    vy
    cE
    wral
    #
    @35
    wps
    bnj1280.7
    wph
    @35
    vd
    cB
    wph
    @0
    vd
    cv
    #
    wfn
    #
    @35
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
    bnj1280.1
    bnj1280.2
    bnj1280.3
    bnj1280.4
    bnj1280.5
    bnj1280.6
    bnj1280.7
    bnj1256
    @40
    cD
    @39
    wss
    #
    @35
    @40
    @0
    cdm
    #
    cD
    @39
    cD
    @42
    @4
    cdm
    #
    bnj1280.4
    bnj1292
    @39
    @0
    fndm
    syl5sseq
    @39
    cD
    @0
    fnssres
    mpdan
    bnj31
    bnj1265
    bnj835
    wph
    @37
    @38
    @36
    wps
    bnj1280.7
    wph
    @36
    vd
    cB
    wph
    @4
    @39
    wfn
    #
    @36
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
    bnj1280.1
    bnj1280.2
    bnj1280.3
    bnj1280.4
    bnj1280.5
    bnj1280.6
    bnj1280.7
    bnj1259
    @44
    @41
    @36
    @44
    @43
    cD
    @39
    cD
    @42
    @43
    bnj1280.4
    bnj1293
    @39
    @4
    fndm
    syl5sseq
    @39
    cD
    @4
    fnssres
    mpdan
    bnj31
    bnj1265
    bnj835
    @19
    vz
    cD
    @2
    @8
    @10
    fvreseq
    syl21anc
    bitr3d
    mpbird
end
