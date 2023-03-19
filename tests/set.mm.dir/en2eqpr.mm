include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "cfn.mm"
include "wss.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "simpl1.mm"
include "enfii.mm"
include "sylancr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "prssi.mm"
include "syl2anc.mm"
include "pr2nelem.mm"
include "3expa.mm"
include "3adantl1.mm"
include "ensymd.mm"
include "entr.mm"
include "fisseneq.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "ex.mm"

theorem en2eqpr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( C ~~ 2o /\ A e. C /\ B e. C ) -> ( A =/= B -> C = { A , B } ) )

  proof
    cC
    c2o
    cen
    wbr
    #
    cA
    cC
    wcel
    #
    cB
    cC
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    cC
    cA
    cB
    cpr
    #
    wceq
    @3
    @4
    wa
    #
    @5
    cC
    @6
    cC
    cfn
    wcel
    #
    @5
    cC
    wss
    #
    @5
    cC
    cen
    wbr
    #
    @5
    cC
    wceq
    @6
    c2o
    cfn
    wcel
    #
    @0
    @7
    c2o
    com
    wcel
    @10
    2onn
    c2o
    nnfi
    ax-mp
    @0
    @1
    @2
    @4
    simpl1
    #
    cC
    c2o
    enfii
    sylancr
    @6
    @1
    @2
    @8
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    cA
    cB
    cC
    prssi
    syl2anc
    @6
    @5
    c2o
    cen
    wbr
    #
    c2o
    cC
    cen
    wbr
    @9
    @1
    @2
    @4
    @12
    @0
    @1
    @2
    @4
    @12
    cA
    cB
    cC
    cC
    pr2nelem
    3expa
    3adantl1
    @6
    cC
    c2o
    @11
    ensymd
    @5
    c2o
    cC
    entr
    syl2anc
    @5
    cC
    fisseneq
    syl3anc
    eqcomd
    ex
end
