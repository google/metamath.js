include "w-bnj15.mm"
include "cdm.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cuni.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "bnj1436.mm"
include "bnj1299.mm"
include "fndm.mm"
include "bnj31.mm"
include "bnj1196.mm"
include "c-bnj14.mm"
include "simpld.mm"
include "anim1i.mm"
include "bnj593.mm"
include "sseq1.mm"
include "biimparc.mm"
include "bnj937.mm"
include "sselda.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "bnj1317.mm"
include "bnj1400.mm"
include "eleq2s.mm"
include "dmeqi.mm"
include "ssriv.mm"
include "a1i.mm"
include "csn.mm"
include "c-bnj18.mm"
include "cun.mm"
include "bnj1493.mm"
include "vsnid.mm"
include "elun1.mm"
include "ax-mp.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "reximi.mm"
include "ralimi.mm"
include "syl.mm"
include "ralbii.mm"
include "sylibr.mm"
include "nfcv.mm"
include "bnj1309.mm"
include "bnj1307.mm"
include "nfcii.mm"
include "nfiun.mm"
include "dfss3f.mm"
include "syl6sseqr.mm"
include "eqssd.mm"

theorem bnj1498
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
  let vt: setvar t
  let vz: setvar z
  let vw: setvar w
  assume bnj1498.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1498.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1498.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1498.4: |- F = U. C

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
  disjoint A t
  disjoint d t
  disjoint f t
  disjoint t x
  disjoint A z
  disjoint f z
  disjoint B t
  disjoint C t
  disjoint C w
  disjoint t w
  disjoint F z
  disjoint f w
  assert |- ( R _FrSe A -> dom F = A )

  proof
    cA
    cR
    w-bnj15
    #
    cF
    cdm
    #
    cA
    @1
    cA
    wss
    @0
    vz
    @1
    cA
    vz
    cv
    #
    cA
    wcel
    #
    @2
    cC
    cuni
    #
    cdm
    #
    @1
    @3
    @2
    vf
    cC
    vf
    cv
    #
    cdm
    #
    ciun
    #
    @5
    @2
    @8
    wcel
    @2
    @7
    wcel
    #
    vf
    cC
    wrex
    @3
    vf
    @2
    cC
    @7
    eliun
    @9
    @3
    vf
    cC
    @6
    cC
    wcel
    #
    @7
    cA
    @2
    @10
    @7
    cA
    wss
    #
    vd
    @10
    vd
    cv
    #
    cA
    wss
    #
    @7
    @12
    wceq
    #
    wa
    #
    @11
    vd
    @10
    @12
    cB
    wcel
    #
    @14
    wa
    @15
    vd
    @10
    @14
    vd
    cB
    @10
    @6
    @12
    wfn
    #
    @14
    vd
    cB
    @10
    @17
    vx
    cv
    #
    @6
    cfv
    cY
    cG
    cfv
    wceq
    vx
    @12
    wral
    #
    vd
    cB
    @17
    @19
    wa
    vd
    cB
    wrex
    #
    vf
    cC
    bnj1498.3
    bnj1436
    bnj1299
    @12
    @6
    fndm
    bnj31
    bnj1196
    @16
    @13
    @14
    @16
    @13
    cA
    cR
    @18
    c-bnj14
    @12
    wss
    vx
    @12
    wral
    #
    @13
    @21
    wa
    vd
    cB
    bnj1498.1
    bnj1436
    simpld
    anim1i
    bnj593
    @14
    @11
    @13
    @7
    @12
    cA
    sseq1
    biimparc
    bnj593
    bnj937
    sselda
    rexlimiva
    sylbi
    vf
    vw
    cC
    @20
    vf
    vw
    cC
    bnj1498.3
    bnj1317
    bnj1400
    #
    eleq2s
    cF
    @4
    bnj1498.4
    dmeqi
    #
    eleq2s
    ssriv
    a1i
    @0
    cA
    @5
    @1
    @0
    cA
    @8
    @5
    @0
    @18
    @8
    wcel
    #
    vx
    cA
    wral
    #
    cA
    @8
    wss
    @0
    @18
    @7
    wcel
    #
    vf
    cC
    wrex
    #
    vx
    cA
    wral
    #
    @25
    @0
    @7
    @18
    csn
    #
    cA
    cR
    @18
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
    @28
    vx
    cA
    cB
    cC
    cR
    vf
    cG
    cY
    vd
    bnj1498.1
    bnj1498.2
    bnj1498.3
    bnj1493
    @33
    @27
    vx
    cA
    @32
    @26
    vf
    cC
    @32
    @26
    @18
    @31
    wcel
    #
    @18
    @29
    wcel
    @34
    vx
    vsnid
    @18
    @29
    @30
    elun1
    ax-mp
    @7
    @31
    @18
    eleq2
    mpbiri
    reximi
    ralimi
    syl
    @24
    @27
    vx
    cA
    vf
    @18
    cC
    @7
    eliun
    ralbii
    sylibr
    vx
    cA
    @8
    vx
    cA
    nfcv
    vf
    vx
    cC
    @7
    vx
    vt
    cC
    vx
    vt
    cB
    cC
    vf
    cG
    cY
    vd
    bnj1498.3
    vx
    vt
    cA
    cB
    cR
    vd
    bnj1498.1
    bnj1309
    bnj1307
    nfcii
    vx
    @7
    nfcv
    nfiun
    dfss3f
    sylibr
    @22
    syl6sseqr
    @23
    syl6sseqr
    eqssd
end
