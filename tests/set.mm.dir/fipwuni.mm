include "cvv.mm"
include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "uniexg.mm"
include "pwexg.mm"
include "syl.mm"
include "pwuni.mm"
include "fiss.mm"
include "sylancl.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "wceq.mm"
include "ssinss1.mm"
include "vex.mm"
include "elpw.mm"
include "inex1.mm"
include "3imtr4i.mm"
include "adantr.mm"
include "rgen2a.mm"
include "wb.mm"
include "inficl.mm"
include "mpbii.mm"
include "sseqtrd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem fipwuni
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V


  assert |- ( fi ` A ) C_ ~P U. A

  proof
    cA
    cvv
    wcel
    #
    cA
    cfi
    cfv
    #
    cA
    cuni
    #
    cpw
    #
    wss
    @0
    @1
    @3
    cfi
    cfv
    #
    @3
    @0
    @3
    cvv
    wcel
    #
    cA
    @3
    wss
    @1
    @4
    wss
    @0
    @2
    cvv
    wcel
    @5
    cA
    cvv
    uniexg
    @2
    cvv
    pwexg
    syl
    #
    cA
    pwuni
    cA
    @3
    cvv
    fiss
    sylancl
    @0
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    @3
    wcel
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    @4
    @3
    wceq
    #
    @10
    vx
    vy
    @3
    @7
    @3
    wcel
    #
    @10
    @8
    @3
    wcel
    @7
    @2
    wss
    @9
    @2
    wss
    @13
    @10
    @7
    @8
    @2
    ssinss1
    @7
    @2
    vx
    vex
    #
    elpw
    @9
    @2
    @7
    @8
    @14
    inex1
    elpw
    3imtr4i
    adantr
    rgen2a
    @0
    @5
    @11
    @12
    wb
    @6
    vx
    vy
    @3
    cvv
    inficl
    syl
    mpbii
    sseqtrd
    @0
    wn
    @1
    c0
    @3
    cA
    cfi
    fvprc
    @3
    0ss
    syl6eqss
    pm2.61i
end
