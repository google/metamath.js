include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cdif.mm"
include "c0.mm"
include "wn.mm"
include "0nelfb.mm"
include "adantr.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "fbasssin.mm"
include "wceq.mm"
include "disjdif.mm"
include "sseq2i.mm"
include "ss0.mm"
include "sylbi.mm"
include "eleq1.mm"
include "biimpac.mm"
include "sylan2.mm"
include "rexlimiva.mm"
include "syl.mm"
include "3expia.mm"
include "mtod.mm"

theorem fbncp
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( ( F e. ( fBas ` X ) /\ A e. F ) -> -. ( B \ A ) e. F )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    wa
    cB
    cA
    cdif
    #
    cF
    wcel
    #
    c0
    cF
    wcel
    #
    @0
    @4
    wn
    @1
    cX
    cF
    0nelfb
    adantr
    @0
    @1
    @3
    @4
    @0
    @1
    @3
    w3a
    vx
    cv
    #
    cA
    @2
    cin
    #
    wss
    #
    vx
    cF
    wrex
    @4
    vx
    cA
    @2
    cF
    cX
    fbasssin
    @7
    @4
    vx
    cF
    @7
    @5
    cF
    wcel
    #
    @5
    c0
    wceq
    #
    @4
    @7
    @5
    c0
    wss
    @9
    @6
    c0
    @5
    cA
    cB
    disjdif
    sseq2i
    @5
    ss0
    sylbi
    @9
    @8
    @4
    @5
    c0
    cF
    eleq1
    biimpac
    sylan2
    rexlimiva
    syl
    3expia
    mtod
end
