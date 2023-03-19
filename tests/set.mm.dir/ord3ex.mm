include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "ctp.mm"
include "cun.mm"
include "cvv.mm"
include "df-tp.mm"
include "cpw.mm"
include "pwpr.mm"
include "pp0ex.mm"
include "pwex.mm"
include "eqeltrri.mm"
include "wss.mm"
include "snsspr2.mm"
include "unss2.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "eqeltri.mm"

theorem ord3ex



  assert |- { (/) , { (/) } , { (/) , { (/) } } } e. _V

  proof
    c0
    c0
    csn
    #
    c0
    @0
    cpr
    #
    ctp
    @1
    @1
    csn
    #
    cun
    #
    cvv
    c0
    @0
    @1
    df-tp
    @3
    @1
    @0
    csn
    #
    @1
    cpr
    #
    cun
    #
    @1
    cpw
    @6
    cvv
    c0
    @0
    pwpr
    @1
    pp0ex
    pwex
    eqeltrri
    @2
    @5
    wss
    @3
    @6
    wss
    @4
    @1
    snsspr2
    @2
    @5
    @1
    unss2
    ax-mp
    ssexi
    eqeltri
end
