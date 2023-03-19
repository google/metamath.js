include "cn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "nnwo.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfral.mm"
include "weq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "breq2.mm"
include "cbvralf.mm"
include "syl6bb.mm"
include "cbvrexf.mm"
include "sylib.mm"

theorem nnwof
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  assume nnwof.1: |- F/_ x A
  assume nnwof.2: |- F/_ y A

  disjoint x y
  disjoint w x
  disjoint v x
  disjoint w y
  disjoint v y
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ( ( A C_ NN /\ A =/= (/) ) -> E. x e. A A. y e. A x <_ y )

  proof
    cA
    cn
    wss
    cA
    c0
    wne
    wa
    vw
    cv
    #
    vv
    cv
    #
    cle
    wbr
    #
    vv
    cA
    wral
    #
    vw
    cA
    wrex
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    vw
    vv
    cA
    nnwo
    @3
    @7
    vw
    vx
    cA
    vw
    cA
    nfcv
    nnwof.1
    @2
    vx
    vv
    cA
    nnwof.1
    @2
    vx
    nfv
    nfral
    @7
    vw
    nfv
    vw
    vx
    weq
    #
    @3
    @4
    @1
    cle
    wbr
    #
    vv
    cA
    wral
    @7
    @8
    @2
    @9
    vv
    cA
    @0
    @4
    @1
    cle
    breq1
    ralbidv
    @9
    @6
    vv
    vy
    cA
    vv
    cA
    nfcv
    nnwof.2
    @9
    vy
    nfv
    @6
    vv
    nfv
    @1
    @5
    @4
    cle
    breq2
    cbvralf
    syl6bb
    cbvrexf
    sylib
end
