include "com.mm"
include "wss.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cale.mm"
include "con0.mm"
include "wrex.mm"
include "wa.mm"
include "crab.mm"
include "cint.mm"
include "wcel.mm"
include "simpl.mm"
include "cardaleph.mm"
include "sseq2d.mm"
include "alephgeom.mm"
include "syl6bbr.mm"
include "mpbid.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "alephcard.mm"
include "id.mm"
include "3eqtr4a.mm"
include "rexlimivw.mm"
include "impbid1.mm"

theorem cardalephex
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( _om C_ A -> ( ( card ` A ) = A <-> E. x e. On A = ( aleph ` x ) ) )

  proof
    com
    cA
    wss
    #
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    cA
    vx
    cv
    #
    cale
    cfv
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @0
    @2
    @6
    @0
    @2
    wa
    #
    cA
    vy
    cv
    cale
    cfv
    wss
    vy
    con0
    crab
    cint
    #
    con0
    wcel
    #
    cA
    @8
    cale
    cfv
    #
    wceq
    #
    @6
    @7
    @0
    @9
    @0
    @2
    simpl
    @7
    @0
    com
    @10
    wss
    @9
    @7
    cA
    @10
    com
    vy
    cA
    cardaleph
    #
    sseq2d
    @8
    alephgeom
    syl6bbr
    mpbid
    @12
    @5
    @11
    vx
    @8
    con0
    @3
    @8
    wceq
    @4
    @10
    cA
    @3
    @8
    cale
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ex
    @5
    @2
    vx
    con0
    @5
    @4
    ccrd
    cfv
    @4
    @1
    cA
    @3
    alephcard
    cA
    @4
    ccrd
    fveq2
    @5
    id
    3eqtr4a
    rexlimivw
    impbid1
end
