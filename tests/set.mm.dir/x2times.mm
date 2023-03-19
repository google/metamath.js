include "cxr.mm"
include "wcel.mm"
include "c2.mm"
include "cxmu.mm"
include "co.mm"
include "c1.mm"
include "cxad.mm"
include "caddc.mm"
include "df-2.mm"
include "cr.mm"
include "wceq.mm"
include "1re.mm"
include "rexadd.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "oveq1i.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "rexri.mm"
include "0le1.mm"
include "pm3.2i.mm"
include "xadddi2r.mm"
include "mp3an12.mm"
include "xmulid2.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem x2times
  let cA: class A


  assert |- ( A e. RR* -> ( 2 *e A ) = ( A +e A ) )

  proof
    cA
    cxr
    wcel
    #
    c2
    cA
    cxmu
    co
    c1
    c1
    cxad
    co
    #
    cA
    cxmu
    co
    #
    cA
    cA
    cxad
    co
    #
    c2
    @1
    cA
    cxmu
    c2
    c1
    c1
    caddc
    co
    #
    @1
    df-2
    c1
    cr
    wcel
    #
    @5
    @1
    @4
    wceq
    1re
    1re
    c1
    c1
    rexadd
    mp2an
    eqtr4i
    oveq1i
    @0
    @2
    c1
    cA
    cxmu
    co
    #
    @6
    cxad
    co
    #
    @3
    c1
    cxr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    wa
    #
    @10
    @0
    @2
    @7
    wceq
    @8
    @9
    c1
    1re
    rexri
    0le1
    pm3.2i
    #
    @11
    c1
    c1
    cA
    xadddi2r
    mp3an12
    @0
    @6
    cA
    @6
    cA
    cxad
    cA
    xmulid2
    #
    @12
    oveq12d
    eqtrd
    syl5eq
end
