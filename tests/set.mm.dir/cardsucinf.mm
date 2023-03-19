include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "wa.mm"
include "ccrd.mm"
include "cfv.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "infensuc.mm"
include "carden2b.mm"
include "syl.mm"
include "eqcomd.mm"

theorem cardsucinf
  let cA: class A


  assert |- ( ( A e. On /\ _om C_ A ) -> ( card ` suc A ) = ( card ` A ) )

  proof
    cA
    con0
    wcel
    com
    cA
    wss
    wa
    #
    cA
    ccrd
    cfv
    #
    cA
    csuc
    #
    ccrd
    cfv
    #
    @0
    cA
    @2
    cen
    wbr
    @1
    @3
    wceq
    cA
    infensuc
    cA
    @2
    carden2b
    syl
    eqcomd
end
