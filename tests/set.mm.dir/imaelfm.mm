include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "wa.mm"
include "cima.mm"
include "cfm.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "3ad2ant3.mm"
include "ssid.mm"
include "wceq.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "anim12i.mm"
include "wb.mm"
include "elfm2.mm"
include "adantr.mm"
include "mpbird.mm"

theorem imaelfm
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume imaelfm.l: |- L = ( Y filGen B )


  assert |- ( ( ( X e. A /\ B e. ( fBas ` Y ) /\ F : Y --> X ) /\ S e. L ) -> ( F " S ) e. ( ( X FilMap F ) ` B ) )

  proof
    cX
    cA
    wcel
    #
    cB
    cY
    cfbas
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cS
    cL
    wcel
    #
    wa
    cF
    cS
    cima
    #
    cB
    cX
    cF
    cfm
    co
    cfv
    wcel
    #
    @5
    cX
    wss
    #
    cF
    vx
    cv
    #
    cima
    #
    @5
    wss
    #
    vx
    cL
    wrex
    #
    wa
    #
    @3
    @7
    @4
    @11
    @2
    @0
    @7
    @1
    @2
    @5
    cF
    crn
    cX
    cF
    cS
    imassrn
    cY
    cX
    cF
    frn
    syl5ss
    3ad2ant3
    @4
    @5
    @5
    wss
    #
    @11
    @5
    ssid
    @10
    @13
    vx
    cS
    cL
    @8
    cS
    wceq
    @9
    @5
    @5
    @8
    cS
    cF
    imaeq2
    sseq1d
    rspcev
    mpan2
    anim12i
    @3
    @6
    @12
    wb
    @4
    vx
    @5
    cB
    cA
    cF
    cL
    cX
    cY
    imaelfm.l
    elfm2
    adantr
    mpbird
end
