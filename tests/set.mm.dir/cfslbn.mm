include "wlim.mm"
include "wss.mm"
include "ccf.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "uniss.mm"
include "limuni.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "wb.mm"
include "word.mm"
include "con0.mm"
include "limord.mm"
include "ordsson.mm"
include "syl.mm"
include "sstr2.mm"
include "syl5com.mm"
include "ssorduni.mm"
include "syl6.mm"
include "jctird.mm"
include "ordsseleq.mm"
include "mpbid.mm"
include "ord.mm"
include "w3a.mm"
include "cdom.mm"
include "cfslb.mm"
include "domnsym.mm"
include "3expia.mm"
include "syld.mm"
include "con4d.mm"
include "3impia.mm"

theorem cfslbn
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume cfslb.1: |- A e. _V


  assert |- ( ( Lim A /\ B C_ A /\ B ~< ( cf ` A ) ) -> U. B e. A )

  proof
    cA
    wlim
    #
    cB
    cA
    wss
    #
    cB
    cA
    ccf
    cfv
    #
    csdm
    wbr
    #
    cB
    cuni
    #
    cA
    wcel
    #
    @0
    @1
    wa
    #
    @5
    @3
    @6
    @5
    wn
    @4
    cA
    wceq
    #
    @3
    wn
    #
    @6
    @5
    @7
    @6
    @4
    cA
    wss
    #
    @5
    @7
    wo
    #
    @0
    @1
    @9
    @1
    @9
    @0
    @4
    cA
    cuni
    #
    wss
    cB
    cA
    uniss
    @0
    cA
    @11
    @4
    cA
    limuni
    sseq2d
    syl5ibr
    imp
    @0
    @1
    @9
    @10
    wb
    #
    @0
    @1
    @4
    word
    #
    cA
    word
    #
    wa
    @12
    @0
    @1
    @13
    @14
    @0
    @1
    cB
    con0
    wss
    #
    @13
    @0
    cA
    con0
    wss
    #
    @1
    @15
    @0
    @14
    @16
    cA
    limord
    #
    cA
    ordsson
    syl
    cB
    cA
    con0
    sstr2
    syl5com
    cB
    ssorduni
    syl6
    @17
    jctird
    @4
    cA
    ordsseleq
    syl6
    imp
    mpbid
    ord
    @0
    @1
    @7
    @8
    @0
    @1
    @7
    w3a
    @2
    cB
    cdom
    wbr
    @8
    cA
    cB
    cfslb.1
    cfslb
    @2
    cB
    domnsym
    syl
    3expia
    syld
    con4d
    3impia
end
