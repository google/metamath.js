include "cnp.mm"
include "wcel.mm"
include "cltp.mm"
include "wbr.mm"
include "cpp.mm"
include "co.mm"
include "ltrelpr.mm"
include "brel.mm"
include "simpld.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "ltexpri.mm"
include "addclpr.mm"
include "ltaddpr.mm"
include "addasspr.mm"
include "oveq2.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "syl5ib.mm"
include "expd.mm"
include "syl5.mm"
include "com3r.mm"
include "rexlimiv.mm"
include "syl.mm"
include "sylan2i.mm"
include "pm2.43b.mm"

theorem ltaprlem
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( C e. P. -> ( A <P B -> ( C +P. A ) <P ( C +P. B ) ) )

  proof
    cC
    cnp
    wcel
    #
    cA
    cB
    cltp
    wbr
    #
    cC
    cA
    cpp
    co
    #
    cC
    cB
    cpp
    co
    #
    cltp
    wbr
    #
    @1
    @0
    @1
    @4
    @1
    @1
    @0
    cA
    cnp
    wcel
    #
    @4
    @1
    @5
    cB
    cnp
    wcel
    cA
    cB
    cnp
    cnp
    cltp
    ltrelpr
    brel
    simpld
    @1
    cA
    vx
    cv
    #
    cpp
    co
    #
    cB
    wceq
    #
    vx
    cnp
    wrex
    @0
    @5
    wa
    #
    @4
    wi
    #
    vx
    cA
    cB
    ltexpri
    @8
    @10
    vx
    cnp
    @8
    @9
    @6
    cnp
    wcel
    #
    @4
    @9
    @2
    cnp
    wcel
    #
    @8
    @11
    @4
    wi
    cC
    cA
    addclpr
    @8
    @12
    @11
    @4
    @12
    @11
    wa
    @2
    @2
    @6
    cpp
    co
    #
    cltp
    wbr
    @8
    @4
    @2
    @6
    ltaddpr
    @8
    @13
    @3
    @2
    cltp
    @8
    @13
    cC
    @7
    cpp
    co
    @3
    cC
    cA
    @6
    addasspr
    @7
    cB
    cC
    cpp
    oveq2
    syl5eq
    breq2d
    syl5ib
    expd
    syl5
    com3r
    rexlimiv
    syl
    sylan2i
    expd
    pm2.43b
end
