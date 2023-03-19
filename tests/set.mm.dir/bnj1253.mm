include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "wrex.mm"
include "c0.mm"
include "cres.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "bnj1254.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "bnj1256.mm"
include "wss.mm"
include "cdm.mm"
include "bnj1292.mm"
include "fndm.mm"
include "syl5sseq.mm"
include "fnssres.mm"
include "mpdan.mm"
include "bnj31.mm"
include "bnj1265.mm"
include "bnj1259.mm"
include "bnj1293.mm"
include "wa.mm"
include "ssid.mm"
include "fvreseq.mm"
include "mpan2.mm"
include "syl2anc.mm"
include "residm.mm"
include "eqeq12i.mm"
include "df-ral.mm"
include "3bitr3g.mm"
include "fvres.mm"
include "eqeq12d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "syl6bb.mm"
include "necon3abid.mm"
include "wex.mm"
include "df-rex.mm"
include "pm4.61.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "exbii.mm"
include "exnal.mm"
include "3bitr2ri.mm"
include "mpbid.mm"
include "crab.mm"
include "neeq1i.mm"
include "rabn0.mm"
include "bitri.mm"
include "sylibr.mm"

theorem bnj1253
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
  assume bnj1253.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1253.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1253.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1253.4: |- D = ( dom g i^i dom h )
  assume bnj1253.5: |- E = { x e. D | ( g ` x ) =/= ( h ` x ) }
  assume bnj1253.6: |- ( ph <-> ( R _FrSe A /\ g e. C /\ h e. C /\ ( g |` D ) =/= ( h |` D ) ) )
  assume bnj1253.7: |- ( ps <-> ( ph /\ x e. E /\ A. y e. E -. y R x ) )

  disjoint A f
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint B h
  disjoint f h
  disjoint D d
  disjoint D x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint R f
  disjoint Y g
  disjoint Y h
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint f x
  disjoint g x
  disjoint h x
  assert |- ( ph -> E =/= (/) )

  proof
    wph
    vx
    cv
    #
    vg
    cv
    #
    cfv
    #
    @0
    vh
    cv
    #
    cfv
    #
    wne
    #
    vx
    cD
    wrex
    #
    cE
    c0
    wne
    #
    wph
    @1
    cD
    cres
    #
    @3
    cD
    cres
    #
    wne
    #
    @6
    wph
    cA
    cR
    w-bnj15
    @1
    cC
    wcel
    @3
    cC
    wcel
    @10
    bnj1253.6
    bnj1254
    wph
    @10
    @0
    cD
    wcel
    #
    @2
    @4
    wceq
    #
    wi
    #
    vx
    wal
    #
    wn
    #
    @6
    wph
    @14
    @8
    @9
    wph
    @8
    @9
    wceq
    #
    @11
    @0
    @8
    cfv
    #
    @0
    @9
    cfv
    #
    wceq
    #
    wi
    #
    vx
    wal
    #
    @14
    wph
    @8
    cD
    cres
    #
    @9
    cD
    cres
    #
    wceq
    #
    @19
    vx
    cD
    wral
    #
    @16
    @21
    wph
    @8
    cD
    wfn
    #
    @9
    cD
    wfn
    #
    @24
    @25
    wb
    #
    wph
    @26
    vd
    cB
    wph
    @1
    vd
    cv
    #
    wfn
    #
    @26
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
    bnj1253.1
    bnj1253.2
    bnj1253.3
    bnj1253.4
    bnj1253.5
    bnj1253.6
    bnj1253.7
    bnj1256
    @30
    cD
    @29
    wss
    #
    @26
    @30
    @1
    cdm
    #
    cD
    @29
    cD
    @32
    @3
    cdm
    #
    bnj1253.4
    bnj1292
    @29
    @1
    fndm
    syl5sseq
    @29
    cD
    @1
    fnssres
    mpdan
    bnj31
    bnj1265
    wph
    @27
    vd
    cB
    wph
    @3
    @29
    wfn
    #
    @27
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
    bnj1253.1
    bnj1253.2
    bnj1253.3
    bnj1253.4
    bnj1253.5
    bnj1253.6
    bnj1253.7
    bnj1259
    @34
    @31
    @27
    @34
    @33
    cD
    @29
    cD
    @32
    @33
    bnj1253.4
    bnj1293
    @29
    @3
    fndm
    syl5sseq
    @29
    cD
    @3
    fnssres
    mpdan
    bnj31
    bnj1265
    @26
    @27
    wa
    cD
    cD
    wss
    @28
    cD
    ssid
    vx
    cD
    cD
    @8
    @9
    fvreseq
    mpan2
    syl2anc
    @22
    @8
    @23
    @9
    @1
    cD
    residm
    @3
    cD
    residm
    eqeq12i
    @19
    vx
    cD
    df-ral
    3bitr3g
    @20
    @13
    vx
    @11
    @19
    @12
    @11
    @17
    @2
    @18
    @4
    @0
    cD
    @1
    fvres
    @0
    cD
    @3
    fvres
    eqeq12d
    pm5.74i
    albii
    syl6bb
    necon3abid
    @6
    @11
    @5
    wa
    #
    vx
    wex
    @13
    wn
    #
    vx
    wex
    @15
    @5
    vx
    cD
    df-rex
    @36
    @35
    vx
    @36
    @11
    @12
    wn
    #
    wa
    @35
    @11
    @12
    pm4.61
    @5
    @37
    @11
    @2
    @4
    df-ne
    anbi2i
    bitr4i
    exbii
    @13
    vx
    exnal
    3bitr2ri
    syl6bb
    mpbid
    @7
    @5
    vx
    cD
    crab
    #
    c0
    wne
    @6
    cE
    @38
    c0
    bnj1253.5
    neeq1i
    @5
    vx
    cD
    rabn0
    bitri
    sylibr
end
