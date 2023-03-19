include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "cint.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "wex.mm"
include "wne.mm"
include "fbasne0.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "ssv.mm"
include "jctr.mm"
include "eximi.mm"
include "df-rex.mm"
include "sylibr.mm"
include "syl.mm"
include "inteq.mm"
include "int0.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "3ad2ant1.mm"
include "cfi.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
include "elfir.mm"
include "syl13anc.mm"
include "fbssfi.mm"
include "syl2anc.mm"
include "ex.mm"
include "pm2.61dne.mm"

theorem fbssint
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint F x
  disjoint B x
  assert |- ( ( F e. ( fBas ` B ) /\ A C_ F /\ A e. Fin ) -> E. x e. F x C_ |^| A )

  proof
    cF
    cB
    cfbas
    cfv
    #
    wcel
    #
    cA
    cF
    wss
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    vx
    cv
    #
    cA
    cint
    #
    wss
    #
    vx
    cF
    wrex
    #
    cA
    c0
    @1
    @2
    cA
    c0
    wceq
    #
    @8
    wi
    @3
    @1
    @8
    @9
    @5
    cvv
    wss
    #
    vx
    cF
    wrex
    #
    @1
    @5
    cF
    wcel
    #
    vx
    wex
    #
    @11
    @1
    cF
    c0
    wne
    @13
    cB
    cF
    fbasne0
    vx
    cF
    n0
    sylib
    @13
    @12
    @10
    wa
    #
    vx
    wex
    @11
    @12
    @14
    vx
    @12
    @10
    @5
    ssv
    jctr
    eximi
    @10
    vx
    cF
    df-rex
    sylibr
    syl
    @9
    @7
    @10
    vx
    cF
    @9
    @6
    cvv
    @5
    @9
    @6
    c0
    cint
    cvv
    cA
    c0
    inteq
    int0
    syl6eq
    sseq2d
    rexbidv
    syl5ibrcom
    3ad2ant1
    @4
    cA
    c0
    wne
    #
    @8
    @4
    @15
    wa
    #
    @1
    @6
    cF
    cfi
    cfv
    wcel
    #
    @8
    @1
    @2
    @3
    @15
    simpl1
    #
    @16
    @1
    @2
    @15
    @3
    @17
    @18
    @1
    @2
    @3
    @15
    simpl2
    @4
    @15
    simpr
    @1
    @2
    @3
    @15
    simpl3
    cA
    cF
    @0
    elfir
    syl13anc
    vx
    @6
    cF
    cB
    fbssfi
    syl2anc
    ex
    pm2.61dne
end
