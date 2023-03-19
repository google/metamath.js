include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wbr.mm"
include "cv.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "wrex.mm"
include "wi.mm"
include "atom1d.mm"
include "spansncv2.mm"
include "sseq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "imp.mm"
include "sylan2b.mm"
include "atelch.mm"
include "wpss.mm"
include "chjcl.mm"
include "cvpss.mm"
include "syldan.mm"
include "chnle.mm"
include "sylibrd.mm"
include "sylan2.mm"
include "impbid.mm"

theorem chcv1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( -. B C_ A <-> A <oH ( A vH B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    cB
    cA
    wss
    #
    wn
    #
    cA
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    @1
    @0
    vx
    cv
    #
    c0v
    wne
    #
    cB
    @6
    csn
    cspn
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    @3
    @5
    wi
    #
    vx
    cB
    atom1d
    @0
    @11
    @12
    @0
    @10
    @12
    vx
    chil
    @0
    @6
    chil
    wcel
    wa
    #
    @9
    @12
    @7
    @13
    @12
    @9
    @8
    cA
    wss
    #
    wn
    #
    cA
    cA
    @8
    chj
    co
    #
    ccv
    wbr
    #
    wi
    cA
    @6
    spansncv2
    @9
    @3
    @15
    @5
    @17
    @9
    @2
    @14
    cB
    @8
    cA
    sseq1
    notbid
    @9
    @4
    @16
    cA
    ccv
    cB
    @8
    cA
    chj
    oveq2
    breq2d
    imbi12d
    syl5ibrcom
    adantld
    rexlimdva
    imp
    sylan2b
    @1
    @0
    cB
    cch
    wcel
    #
    @5
    @3
    wi
    cB
    atelch
    @0
    @18
    wa
    @5
    cA
    @4
    wpss
    #
    @3
    @0
    @18
    @4
    cch
    wcel
    @5
    @19
    wi
    cA
    cB
    chjcl
    cA
    @4
    cvpss
    syldan
    cA
    cB
    chnle
    sylibrd
    sylan2
    impbid
end
