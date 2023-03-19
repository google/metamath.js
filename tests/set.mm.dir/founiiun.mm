include "wfo.mm"
include "cuni.mm"
include "cv.mm"
include "ciun.mm"
include "cfv.mm"
include "wceq.mm"
include "uniiun.mm"
include "a1i.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "foelrni.mm"
include "syl2anc.mm"
include "wi.mm"
include "eqimss2.mm"
include "reximi.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "iunss2.mm"
include "syl.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "eqssd.mm"
include "eqtrd.mm"

theorem founiiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( F : A -onto-> B -> U. B = U_ x e. A ( F ` x ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cB
    cuni
    #
    vy
    cB
    vy
    cv
    #
    ciun
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    ciun
    #
    @1
    @3
    wceq
    @0
    vy
    cB
    uniiun
    a1i
    @0
    @3
    @6
    @0
    @2
    @5
    wss
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    @3
    @6
    wss
    @0
    @8
    vy
    cB
    @0
    @2
    cB
    wcel
    #
    wa
    #
    @5
    @2
    wceq
    #
    vx
    cA
    wrex
    #
    @8
    @10
    @0
    @9
    @12
    @0
    @9
    simpl
    @0
    @9
    simpr
    vx
    cA
    cB
    cF
    @2
    foelrni
    syl2anc
    @12
    @8
    wi
    @10
    @11
    @7
    vx
    cA
    @2
    @5
    eqimss2
    reximi
    a1i
    mpd
    ralrimiva
    vy
    vx
    cB
    cA
    @2
    @5
    iunss2
    syl
    @0
    @5
    @2
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    @6
    @3
    wss
    @0
    @14
    vx
    cA
    @0
    @4
    cA
    wcel
    wa
    #
    @5
    cB
    wcel
    @5
    @5
    wss
    #
    @14
    @0
    cA
    cB
    @4
    cF
    cA
    cB
    cF
    fof
    ffvelrnda
    @16
    @15
    @5
    ssid
    a1i
    @13
    @16
    vy
    @5
    cB
    @2
    @5
    @5
    sseq2
    rspcev
    syl2anc
    ralrimiva
    vx
    vy
    cA
    cB
    @5
    @2
    iunss2
    syl
    eqssd
    eqtrd
end
