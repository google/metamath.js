include "cupgr.mm"
include "wcel.mm"
include "cpr.mm"
include "wss.mm"
include "w3a.mm"
include "wne.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "upgredg.mm"
include "3adant3.mm"
include "wa.mm"
include "ssprsseq.mm"
include "biimpd.mm"
include "sseq2.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "com23.mm"
include "a1i.mm"
include "rexlimivv.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "imp.mm"

theorem upgredgpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume upgredg.v: |- V = ( Vtx ` G )
  assume upgredg.e: |- E = ( Edg ` G )


  assert |- ( ( ( G e. UPGraph /\ C e. E /\ { A , B } C_ C ) /\ ( A e. U /\ B e. W /\ A =/= B ) ) -> { A , B } = C )

  proof
    cG
    cupgr
    wcel
    #
    cC
    cE
    wcel
    #
    cA
    cB
    cpr
    #
    cC
    wss
    #
    w3a
    #
    cA
    cU
    wcel
    cB
    cW
    wcel
    cA
    cB
    wne
    w3a
    #
    @2
    cC
    wceq
    #
    @4
    cC
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @5
    @6
    wi
    #
    @0
    @1
    @11
    @3
    cC
    cE
    cG
    cV
    va
    vb
    upgredg.v
    upgredg.e
    upgredg
    3adant3
    @3
    @0
    @11
    @12
    wi
    @1
    @11
    @3
    @12
    @10
    @3
    @12
    wi
    #
    va
    vb
    cV
    cV
    @10
    @13
    wi
    @7
    cV
    wcel
    @8
    cV
    wcel
    wa
    @10
    @5
    @3
    @6
    @5
    @3
    @6
    wi
    @10
    @2
    @9
    wss
    #
    @2
    @9
    wceq
    #
    wi
    @5
    @14
    @15
    cA
    cB
    @7
    @8
    cU
    cW
    ssprsseq
    biimpd
    @10
    @3
    @14
    @6
    @15
    cC
    @9
    @2
    sseq2
    cC
    @9
    @2
    eqeq2
    imbi12d
    syl5ibr
    com23
    a1i
    rexlimivv
    com12
    3ad2ant3
    mpd
    imp
end
