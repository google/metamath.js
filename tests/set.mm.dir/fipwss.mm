include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cfi.mm"
include "cfv.mm"
include "cuni.mm"
include "fiuni.mm"
include "sseq1d.mm"
include "sspwuni.mm"
include "3bitr4g.mm"
include "biimpa.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem fipwss
  let cA: class A
  let cX: class X


  assert |- ( A C_ ~P X -> ( fi ` A ) C_ ~P X )

  proof
    cA
    cvv
    wcel
    #
    cA
    cX
    cpw
    #
    wss
    #
    cA
    cfi
    cfv
    #
    @1
    wss
    #
    @0
    @2
    @4
    @0
    cA
    cuni
    #
    cX
    wss
    @3
    cuni
    #
    cX
    wss
    @2
    @4
    @0
    @5
    @6
    cX
    cA
    cvv
    fiuni
    sseq1d
    cA
    cX
    sspwuni
    @3
    cX
    sspwuni
    3bitr4g
    biimpa
    @0
    wn
    #
    @4
    @2
    @7
    @3
    c0
    @1
    cA
    cfi
    fvprc
    @1
    0ss
    syl6eqss
    adantr
    pm2.61ian
end
