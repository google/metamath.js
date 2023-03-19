include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "cfbas.mm"
include "filfbas.mm"
include "fbasssin.mm"
include "syl3an1.mm"
include "wi.mm"
include "wa.mm"
include "inss1.mm"
include "filelss.mm"
include "syl5ss.mm"
include "filss.mm"
include "3exp2.mm"
include "com23.mm"
include "imp.mm"
include "rexlimdv.mm"
include "syldan.mm"
include "3adant3.mm"
include "mpd.mm"

theorem filin
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F /\ B e. F ) -> ( A i^i B ) e. F )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    cB
    cF
    wcel
    #
    w3a
    vx
    cv
    #
    cA
    cB
    cin
    #
    wss
    #
    vx
    cF
    wrex
    #
    @4
    cF
    wcel
    #
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    @1
    @2
    @6
    cF
    cX
    filfbas
    vx
    cA
    cB
    cF
    cX
    fbasssin
    syl3an1
    @0
    @1
    @6
    @7
    wi
    #
    @2
    @0
    @1
    @4
    cX
    wss
    #
    @8
    @0
    @1
    wa
    @4
    cA
    cX
    cA
    cB
    inss1
    cA
    cF
    cX
    filelss
    syl5ss
    @0
    @9
    wa
    @5
    @7
    vx
    cF
    @0
    @9
    @3
    cF
    wcel
    #
    @5
    @7
    wi
    #
    wi
    @0
    @10
    @9
    @11
    @0
    @10
    @9
    @5
    @7
    @3
    @4
    cF
    cX
    filss
    3exp2
    com23
    imp
    rexlimdv
    syldan
    3adant3
    mpd
end
