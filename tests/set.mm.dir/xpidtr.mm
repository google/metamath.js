include "cxp.mm"
include "ccom.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "brxp.mm"
include "simplbi2com.mm"
include "simplbiim.mm"
include "com12.mm"
include "adantr.mm"
include "sylbi.mm"
include "imp.mm"
include "ax-gen.mm"
include "gen2.mm"
include "cotr.mm"
include "mpbir.mm"

theorem xpidtr
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( ( A X. A ) o. ( A X. A ) ) C_ ( A X. A )

  proof
    cA
    cA
    cxp
    #
    @0
    ccom
    @0
    wss
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    @2
    vz
    cv
    #
    @0
    wbr
    #
    wa
    @1
    @4
    @0
    wbr
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @8
    vx
    vy
    @7
    vz
    @3
    @5
    @6
    @3
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    @5
    @6
    wi
    #
    @1
    @2
    cA
    cA
    brxp
    @9
    @11
    @10
    @5
    @9
    @6
    @5
    @10
    @4
    cA
    wcel
    #
    @9
    @6
    wi
    @2
    @4
    cA
    cA
    brxp
    @6
    @9
    @12
    @1
    @4
    cA
    cA
    brxp
    simplbi2com
    simplbiim
    com12
    adantr
    sylbi
    imp
    ax-gen
    gen2
    vx
    vy
    vz
    @0
    cotr
    mpbir
end
