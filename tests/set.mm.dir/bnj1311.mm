include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cres.mm"
include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "w-bnj17.mm"
include "wa.mm"
include "cfv.mm"
include "crab.mm"
include "wbr.mm"
include "wral.mm"
include "wss.mm"
include "c0.mm"
include "wrex.mm"
include "biid.mm"
include "bnj1232.mm"
include "ssrab2.mm"
include "cdm.mm"
include "cin.mm"
include "wfn.mm"
include "c-bnj14.mm"
include "cop.mm"
include "cab.mm"
include "bnj1235.mm"
include "eqid.mm"
include "bnj1234.mm"
include "syl6eleq.mm"
include "abid.mm"
include "bnj1238.mm"
include "bnj1196.mm"
include "abeq2i.mm"
include "simplbi.mm"
include "fndm.mm"
include "bnj1241.mm"
include "bnj593.mm"
include "bnj937.mm"
include "ssinss1.mm"
include "3syl.mm"
include "syl5eqss.mm"
include "syl5ss.mm"
include "bnj1253.mm"
include "nfrab1.mm"
include "nfcrii.mm"
include "bnj1228.mm"
include "syl3anc.mm"
include "ax-5.mm"
include "bnj1309.mm"
include "bnj1307.mm"
include "hblem.mm"
include "bnj982.mm"
include "bnj1521.mm"
include "simp2.mm"
include "bnj1279.mm"
include "3adant1.mm"
include "bnj1280.mm"
include "bnj1296.mm"
include "bnj1538.mm"
include "necon2bi.mm"
include "syl.mm"
include "bnj1304.mm"
include "df-bnj17.mm"
include "mtbi.mm"
include "imnani.mm"
include "nne.mm"
include "sylib.mm"

theorem bnj1311
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  assume bnj1311.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1311.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1311.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1311.4: |- D = ( dom g i^i dom h )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint B g
  disjoint f g
  disjoint B h
  disjoint f h
  disjoint D d
  disjoint D x
  disjoint G d
  disjoint G f
  disjoint G g
  disjoint d g
  disjoint G h
  disjoint d h
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint Y g
  disjoint Y h
  disjoint g x
  disjoint h x
  disjoint A w
  disjoint A z
  disjoint d w
  disjoint d z
  disjoint f w
  disjoint f z
  disjoint w x
  disjoint x z
  disjoint w z
  disjoint A y
  disjoint x y
  disjoint B w
  disjoint B z
  disjoint g w
  disjoint g z
  disjoint h z
  disjoint D y
  disjoint D w
  disjoint D z
  disjoint w y
  disjoint y z
  disjoint R y
  disjoint g y
  disjoint h y
  disjoint C w
  assert |- ( ( R _FrSe A /\ g e. C /\ h e. C ) -> ( g |` D ) = ( h |` D ) )

  proof
    cA
    cR
    w-bnj15
    #
    vg
    cv
    #
    cC
    wcel
    #
    vh
    cv
    #
    cC
    wcel
    #
    w3a
    #
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
    wn
    @6
    @7
    wceq
    @5
    @8
    @0
    @2
    @4
    @8
    w-bnj17
    #
    @5
    @8
    wa
    @9
    @9
    vx
    cv
    #
    @10
    @1
    cfv
    #
    @10
    @3
    cfv
    #
    wne
    #
    vx
    cD
    crab
    #
    wcel
    #
    vy
    cv
    @10
    cR
    wbr
    wn
    vy
    @14
    wral
    #
    w3a
    #
    @15
    vx
    @16
    @9
    @17
    vx
    @14
    @9
    @0
    @14
    cA
    wss
    @14
    c0
    wne
    @16
    vx
    @14
    wrex
    @9
    @0
    @2
    @4
    @8
    @9
    biid
    #
    bnj1232
    @9
    @14
    cD
    cA
    @13
    vx
    cD
    ssrab2
    @9
    cD
    @1
    cdm
    #
    @3
    cdm
    #
    cin
    #
    cA
    bnj1311.4
    @9
    @1
    @1
    vd
    cv
    #
    wfn
    #
    @11
    @10
    @1
    cA
    cR
    @10
    c-bnj14
    #
    cres
    cop
    #
    cG
    cfv
    wceq
    vx
    @22
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
    wcel
    #
    @19
    cA
    wss
    #
    @21
    cA
    wss
    @9
    @1
    cC
    @28
    @9
    @0
    @2
    @4
    @8
    @18
    bnj1235
    vx
    cA
    cB
    cC
    @28
    cR
    vf
    vg
    cG
    cY
    @25
    vd
    bnj1311.2
    bnj1311.3
    @25
    eqid
    #
    @28
    eqid
    #
    bnj1234
    syl6eleq
    @29
    @30
    vd
    @29
    @22
    cB
    wcel
    #
    @23
    wa
    @30
    vd
    @29
    @23
    vd
    cB
    @29
    @23
    @26
    vd
    cB
    @27
    vg
    abid
    bnj1238
    bnj1196
    @33
    @23
    @22
    cA
    @19
    @33
    @22
    cA
    wss
    #
    @24
    @22
    wss
    vx
    @22
    wral
    #
    @34
    @35
    wa
    vd
    cB
    bnj1311.1
    abeq2i
    simplbi
    @22
    @1
    fndm
    bnj1241
    bnj593
    bnj937
    @19
    @20
    cA
    ssinss1
    3syl
    syl5eqss
    syl5ss
    @9
    @17
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
    @14
    cG
    cY
    vd
    bnj1311.1
    bnj1311.2
    bnj1311.3
    bnj1311.4
    @14
    eqid
    #
    @18
    @17
    biid
    #
    bnj1253
    vx
    vy
    vz
    cA
    @14
    cR
    vx
    vz
    @14
    @13
    vx
    cD
    nfrab1
    nfcrii
    bnj1228
    syl3anc
    @37
    @0
    @2
    @4
    @8
    vx
    @0
    vx
    ax-5
    vx
    vw
    vg
    cC
    vx
    vw
    cB
    cC
    vf
    cG
    cY
    vd
    bnj1311.3
    vx
    vw
    cA
    cB
    cR
    vd
    bnj1311.1
    bnj1309
    bnj1307
    #
    hblem
    vx
    vw
    vh
    cC
    @38
    hblem
    @8
    vx
    ax-5
    bnj982
    bnj1521
    @9
    @15
    @16
    simp2
    @17
    @11
    @12
    wceq
    @15
    wn
    @9
    @17
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
    @14
    cG
    @28
    @3
    @22
    wfn
    @12
    @10
    @3
    @24
    cres
    cop
    #
    cG
    cfv
    wceq
    vx
    @22
    wral
    wa
    vd
    cB
    wrex
    vh
    cab
    #
    @39
    cY
    @25
    vd
    bnj1311.1
    bnj1311.2
    bnj1311.3
    bnj1311.4
    @36
    @18
    @37
    @9
    @17
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
    @14
    cG
    cY
    vd
    bnj1311.1
    bnj1311.2
    bnj1311.3
    bnj1311.4
    @36
    @18
    @37
    @15
    @16
    @24
    @14
    cin
    c0
    wceq
    @9
    @9
    @17
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
    @14
    cG
    cY
    vd
    bnj1311.1
    bnj1311.2
    bnj1311.3
    bnj1311.4
    @36
    @18
    @37
    bnj1279
    3adant1
    bnj1280
    @31
    @32
    @39
    eqid
    @40
    eqid
    bnj1296
    @15
    @11
    @12
    @13
    vx
    @14
    cD
    @36
    bnj1538
    necon2bi
    syl
    bnj1304
    @0
    @2
    @4
    @8
    df-bnj17
    mtbi
    imnani
    @6
    @7
    nne
    sylib
end
