include "wf.mm"
include "wsmo.mm"
include "word.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "wfn.mm"
include "simpl1.mm"
include "ffn.mm"
include "syl.mm"
include "simpl2.mm"
include "smodm2.mm"
include "syl2anc.mm"
include "ordelord.mm"
include "sylancom.mm"
include "simpl3.mm"
include "simpr.mm"
include "smogt.mm"
include "syl3anc.mm"
include "ffvelrn.mm"
include "3ad2antl1.mm"
include "ordtr2.mm"
include "imp.mm"
include "syl22anc.mm"
include "ex.mm"
include "ssrdv.mm"

theorem smorndom
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( ( F : A --> B /\ Smo F /\ Ord B ) -> A C_ B )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    wsmo
    #
    cB
    word
    #
    w3a
    #
    vx
    cA
    cB
    @3
    vx
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    @3
    @5
    wa
    #
    @4
    word
    #
    @2
    @4
    @4
    cF
    cfv
    #
    wss
    #
    @9
    cB
    wcel
    #
    @6
    @3
    @5
    cA
    word
    #
    @8
    @7
    cF
    cA
    wfn
    #
    @1
    @12
    @7
    @0
    @13
    @0
    @1
    @2
    @5
    simpl1
    cA
    cB
    cF
    ffn
    syl
    #
    @0
    @1
    @2
    @5
    simpl2
    #
    cA
    cF
    smodm2
    syl2anc
    cA
    @4
    ordelord
    sylancom
    @0
    @1
    @2
    @5
    simpl3
    @7
    @13
    @1
    @5
    @10
    @14
    @15
    @3
    @5
    simpr
    cA
    @4
    cF
    smogt
    syl3anc
    @0
    @1
    @5
    @11
    @2
    cA
    cB
    @4
    cF
    ffvelrn
    3ad2antl1
    @8
    @2
    wa
    @10
    @11
    wa
    @6
    @4
    @9
    cB
    ordtr2
    imp
    syl22anc
    ex
    ssrdv
end
