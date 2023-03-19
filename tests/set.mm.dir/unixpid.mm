include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cuni.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "wi.mm"
include "unieq.mm"
include "unieqd.mm"
include "uni0.mm"
include "unieqi.mm"
include "eqtri.mm"
include "wa.mm"
include "eqtr.mm"
include "expcom.mm"
include "eqcoms.mm"
include "syl5com.mm"
include "sylancl.mm"
include "mpcom.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "xpnz.mm"
include "cun.mm"
include "unixp.mm"
include "unidm.mm"
include "sylbi.mm"
include "sylancbr.mm"
include "pm2.61i.mm"

theorem unixpid
  let cA: class A


  assert |- U. U. ( A X. A ) = A

  proof
    cA
    c0
    wceq
    #
    cA
    cA
    cxp
    #
    cuni
    #
    cuni
    #
    cA
    wceq
    #
    @1
    c0
    wceq
    #
    @0
    @4
    @0
    @1
    c0
    cA
    cxp
    c0
    cA
    c0
    cA
    xpeq1
    cA
    0xp
    syl6eq
    @5
    @3
    c0
    cuni
    #
    cuni
    #
    wceq
    #
    @7
    c0
    wceq
    #
    @0
    @4
    wi
    @5
    @2
    @6
    @1
    c0
    unieq
    unieqd
    @7
    @6
    c0
    @6
    c0
    uni0
    unieqi
    uni0
    eqtri
    @8
    @9
    wa
    @3
    c0
    wceq
    #
    @0
    @4
    @3
    @7
    c0
    eqtr
    @10
    @4
    wi
    c0
    cA
    @10
    c0
    cA
    wceq
    @4
    @3
    c0
    cA
    eqtr
    expcom
    eqcoms
    syl5com
    sylancl
    mpcom
    @0
    wn
    cA
    c0
    wne
    #
    @11
    @4
    cA
    c0
    df-ne
    #
    @12
    @11
    @11
    wa
    @1
    c0
    wne
    #
    @4
    cA
    cA
    xpnz
    @13
    @3
    cA
    cA
    cun
    cA
    cA
    cA
    unixp
    cA
    unidm
    syl6eq
    sylbi
    sylancbr
    pm2.61i
end
