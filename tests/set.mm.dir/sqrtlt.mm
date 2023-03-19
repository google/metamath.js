include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "csqrt.mm"
include "cfv.mm"
include "clt.mm"
include "wb.mm"
include "sqrtle.mm"
include "ancoms.mm"
include "notbid.mm"
include "simpll.mm"
include "simprl.mm"
include "ltnled.mm"
include "resqrtcl.mm"
include "adantr.mm"
include "adantl.mm"
include "3bitr4d.mm"

theorem sqrtlt
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( A < B <-> ( sqrt ` A ) < ( sqrt ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cB
    cA
    cle
    wbr
    #
    wn
    cB
    csqrt
    cfv
    #
    cA
    csqrt
    cfv
    #
    cle
    wbr
    #
    wn
    cA
    cB
    clt
    wbr
    @9
    @8
    clt
    wbr
    @6
    @7
    @10
    @5
    @2
    @7
    @10
    wb
    cB
    cA
    sqrtle
    ancoms
    notbid
    @6
    cA
    cB
    @0
    @1
    @5
    simpll
    @2
    @3
    @4
    simprl
    ltnled
    @6
    @9
    @8
    @2
    @9
    cr
    wcel
    @5
    cA
    resqrtcl
    adantr
    @5
    @8
    cr
    wcel
    @2
    cB
    resqrtcl
    adantl
    ltnled
    3bitr4d
end
