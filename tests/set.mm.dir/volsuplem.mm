include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "cn.mm"
include "wral.mm"
include "wcel.mm"
include "cuz.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "eluznn.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "rspccva.mm"
include "sylan2.mm"
include "anassrs.mm"
include "sstr2.mm"
include "syl5com.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "com12.mm"
include "impr.mm"

theorem volsuplem
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vx: setvar x

  disjoint F n
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint n x
  disjoint F x
  disjoint A k
  disjoint A x
  disjoint B x
  assert |- ( ( A. n e. NN ( F ` n ) C_ ( F ` ( n + 1 ) ) /\ ( A e. NN /\ B e. ( ZZ>= ` A ) ) ) -> ( F ` A ) C_ ( F ` B ) )

  proof
    vn
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
    vn
    cn
    wral
    #
    cA
    cn
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
    vx
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
    vk
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
    vx
    vk
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
    @13
    @17
    wceq
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
    @12
    @27
    @19
    @22
    wi
    @12
    @27
    wa
    @18
    @21
    wss
    #
    @19
    @22
    @5
    @6
    @27
    @28
    @6
    @27
    wa
    @5
    @17
    cn
    wcel
    @28
    @17
    cA
    eluznn
    @4
    @28
    vn
    @17
    cn
    @0
    @17
    wceq
    #
    @1
    @18
    @3
    @21
    @0
    @17
    cF
    fveq2
    @29
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
    rspccva
    sylan2
    anassrs
    @9
    @18
    @21
    sstr2
    syl5com
    expcom
    a2d
    uzind4
    com12
    impr
end
