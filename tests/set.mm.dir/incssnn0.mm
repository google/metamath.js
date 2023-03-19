include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "cn0.mm"
include "wral.mm"
include "wcel.mm"
include "cuz.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "eluznn0.mm"
include "ancoms.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "sstr2.mm"
include "com12.mm"
include "syl6.mm"
include "a2d.mm"
include "uzind4.mm"
include "3impia.mm"

theorem incssnn0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b

  disjoint F x
  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint F a
  disjoint F b
  disjoint a x
  disjoint b x
  assert |- ( ( A. x e. NN0 ( F ` x ) C_ ( F ` ( x + 1 ) ) /\ A e. NN0 /\ B e. ( ZZ>= ` A ) ) -> ( F ` A ) C_ ( F ` B ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    vx
    cn0
    wral
    #
    cA
    cn0
    wcel
    #
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wss
    #
    @8
    @5
    @6
    wa
    #
    @11
    @12
    @9
    va
    cv
    #
    cF
    cfv
    #
    wss
    #
    wi
    @12
    @9
    @9
    wss
    #
    wi
    @12
    @9
    vb
    cv
    #
    cF
    cfv
    #
    wss
    #
    wi
    @12
    @9
    @17
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wss
    #
    wi
    @12
    @11
    wi
    va
    vb
    cA
    cB
    @13
    cA
    wceq
    #
    @15
    @16
    @12
    @23
    @14
    @9
    @9
    @13
    cA
    cF
    fveq2
    sseq2d
    imbi2d
    va
    vb
    weq
    #
    @15
    @19
    @12
    @24
    @14
    @18
    @9
    @13
    @17
    cF
    fveq2
    sseq2d
    imbi2d
    @13
    @20
    wceq
    #
    @15
    @22
    @12
    @25
    @14
    @21
    @9
    @13
    @20
    cF
    fveq2
    sseq2d
    imbi2d
    @13
    cB
    wceq
    #
    @15
    @11
    @12
    @26
    @14
    @10
    @9
    @13
    cB
    cF
    fveq2
    sseq2d
    imbi2d
    @16
    cA
    cz
    wcel
    @12
    @9
    ssid
    2a1i
    @17
    @7
    wcel
    #
    @12
    @19
    @22
    @27
    @12
    @18
    @21
    wss
    #
    @19
    @22
    wi
    @27
    @6
    @5
    @28
    @27
    @6
    @5
    @28
    @27
    @6
    wa
    @17
    cn0
    wcel
    #
    @5
    @28
    wi
    @6
    @27
    @29
    @17
    cA
    eluznn0
    ancoms
    @4
    @28
    vx
    @17
    cn0
    vx
    vb
    weq
    #
    @1
    @18
    @3
    @21
    @0
    @17
    cF
    fveq2
    @30
    @2
    @20
    cF
    @0
    @17
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    rspcv
    syl
    expimpd
    ancomsd
    @19
    @28
    @22
    @9
    @18
    @21
    sstr2
    com12
    syl6
    a2d
    uzind4
    com12
    3impia
end
