include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "wrex.mm"
include "c-bnj14.mm"
include "fveq2.mm"
include "simpl2.mm"
include "sylib.mm"
include "sylan9eqr.mm"
include "bnj213.mm"
include "syl6eqss.mm"
include "wi.mm"
include "ciun.mm"
include "r19.29r.mm"
include "eleq1.mm"
include "biimpd.mm"
include "eqeq1d.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "syl6bir.mm"
include "imim12d.mm"
include "imp.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "com3l.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "imp31.mm"
include "wo.mm"
include "simpr.mm"
include "simpl1.mm"
include "elnn.mm"
include "syl2anc.mm"
include "nn0suc.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "sseq1d.mm"
include "cbvralv.mm"

theorem bnj517
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cX: class X
  let vm: setvar m
  assume bnj517.1: |- ( ph <-> ( F ` (/) ) = _pred ( X , A , R ) )
  assume bnj517.2: |- ( ps <-> A. i e. _om ( suc i e. N -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) ) )

  disjoint i n
  disjoint i y
  disjoint A i
  disjoint n y
  disjoint A n
  disjoint A y
  disjoint F i
  disjoint F n
  disjoint N i
  disjoint N n
  disjoint i m
  disjoint m n
  disjoint m y
  disjoint A m
  disjoint F m
  disjoint N m
  disjoint m ph
  disjoint m ps
  assert |- ( ( N e. _om /\ ph /\ ps ) -> A. n e. N ( F ` n ) C_ A )

  proof
    cN
    com
    wcel
    #
    wph
    wps
    w3a
    #
    vm
    cv
    #
    cF
    cfv
    #
    cA
    wss
    #
    vm
    cN
    wral
    vn
    cv
    #
    cF
    cfv
    #
    cA
    wss
    #
    vn
    cN
    wral
    @1
    @4
    vm
    cN
    @1
    @2
    cN
    wcel
    #
    wa
    #
    @2
    c0
    wceq
    #
    @4
    @2
    vi
    cv
    #
    csuc
    #
    wceq
    #
    vi
    com
    wrex
    #
    @9
    @10
    wa
    @3
    cA
    cR
    cX
    c-bnj14
    #
    cA
    @10
    @9
    @3
    c0
    cF
    cfv
    #
    @15
    @2
    c0
    cF
    fveq2
    @9
    wph
    @16
    @15
    wceq
    @0
    wph
    wps
    @8
    simpl2
    bnj517.1
    sylib
    sylan9eqr
    cA
    cR
    cX
    bnj213
    syl6eqss
    @1
    @8
    @14
    @4
    wps
    @0
    @8
    @14
    @4
    wi
    wi
    #
    wph
    wps
    @12
    cN
    wcel
    #
    @12
    cF
    cfv
    #
    vy
    @11
    cF
    cfv
    #
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    #
    @17
    bnj517.2
    @14
    @26
    @8
    @4
    @14
    @26
    @8
    @4
    wi
    #
    @14
    @26
    wa
    @13
    @25
    wa
    #
    vi
    com
    wrex
    @27
    @13
    @25
    vi
    com
    r19.29r
    @28
    @27
    vi
    com
    @13
    @25
    @27
    @13
    @8
    @18
    @24
    @4
    @13
    @8
    @18
    @2
    @12
    cN
    eleq1
    biimpd
    @13
    @24
    @3
    @23
    wceq
    #
    @4
    @13
    @3
    @19
    @23
    @2
    @12
    cF
    fveq2
    eqeq1d
    @29
    @4
    @23
    cA
    wss
    #
    @30
    @22
    cA
    wss
    #
    vy
    @20
    wral
    @31
    vy
    @20
    cA
    cR
    @21
    bnj213
    rgenw
    vy
    @20
    @22
    cA
    iunss
    mpbir
    @3
    @23
    cA
    sseq1
    mpbiri
    syl6bir
    imim12d
    imp
    rexlimivw
    syl
    ex
    com3l
    sylbi
    3ad2ant3
    imp31
    @9
    @2
    com
    wcel
    #
    @10
    @14
    wo
    @9
    @8
    @0
    @32
    @1
    @8
    simpr
    @0
    wph
    wps
    @8
    simpl1
    @2
    cN
    elnn
    syl2anc
    vi
    @2
    nn0suc
    syl
    mpjaodan
    ralrimiva
    @4
    @7
    vm
    vn
    cN
    @2
    @5
    wceq
    @3
    @6
    cA
    @2
    @5
    cF
    fveq2
    sseq1d
    cbvralv
    sylib
end
