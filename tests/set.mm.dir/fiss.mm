include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "cfi.mm"
include "cfv.mm"
include "wi.mm"
include "sstr2.mm"
include "adantl.mm"
include "anim1d.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"
include "cvv.mm"
include "wceq.mm"
include "ssexg.mm"
include "ancoms.mm"
include "dffi2.mm"
include "adantr.mm"
include "3sstr4d.mm"

theorem fiss
  let cA: class A
  let cB: class B
  let cV: class V
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( B e. V /\ A C_ B ) -> ( fi ` A ) C_ ( fi ` B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    vy
    cv
    #
    wss
    #
    vx
    cv
    vz
    cv
    cin
    @3
    wcel
    vz
    @3
    wral
    vx
    @3
    wral
    #
    wa
    #
    vy
    cab
    #
    cint
    #
    cB
    @3
    wss
    #
    @5
    wa
    #
    vy
    cab
    #
    cint
    #
    cA
    cfi
    cfv
    #
    cB
    cfi
    cfv
    #
    @2
    @11
    @7
    wss
    @8
    @12
    wss
    @2
    @10
    @6
    vy
    @2
    @9
    @4
    @5
    @1
    @9
    @4
    wi
    @0
    cA
    cB
    @3
    sstr2
    adantl
    anim1d
    ss2abdv
    @11
    @7
    intss
    syl
    @2
    cA
    cvv
    wcel
    #
    @13
    @8
    wceq
    @1
    @0
    @15
    cA
    cB
    cV
    ssexg
    ancoms
    vx
    vz
    vy
    cA
    cvv
    dffi2
    syl
    @0
    @14
    @12
    wceq
    @1
    vx
    vz
    vy
    cB
    cV
    dffi2
    adantr
    3sstr4d
end
