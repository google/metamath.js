include "cclm.mm"
include "wcel.mm"
include "cz.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cmg.mm"
include "eqid.mm"
include "zlmvsca.mm"
include "eqcomi.mm"
include "clmmulg.mm"
include "eqcomd.mm"
include "3expb.mm"

theorem clmzlmvsca
  let cA: class A
  let cB: class B
  let cG: class G
  let cW: class W
  let cX: class X
  assume zlmclm.w: |- W = ( ZMod ` G )
  assume clmzlmvsca.x: |- X = ( Base ` G )


  assert |- ( ( G e. CMod /\ ( A e. ZZ /\ B e. X ) ) -> ( A ( .s ` G ) B ) = ( A ( .s ` W ) B ) )

  proof
    cG
    cclm
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cG
    cvsca
    cfv
    #
    co
    #
    cA
    cB
    cW
    cvsca
    cfv
    #
    co
    #
    wceq
    @0
    @1
    @2
    w3a
    @6
    @4
    cA
    cB
    @5
    @3
    cX
    cG
    clmzlmvsca.x
    cG
    cmg
    cfv
    #
    @5
    @7
    cG
    cW
    zlmclm.w
    @7
    eqid
    zlmvsca
    eqcomi
    @3
    eqid
    clmmulg
    eqcomd
    3expb
end
