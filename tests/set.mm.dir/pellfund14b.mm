include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cpellfund.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "pellfund14.mm"
include "wa.mm"
include "simpll.mm"
include "cpell1qr.mm"
include "pell1qrss14.mm"
include "pellfundex.mm"
include "sseldd.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "pell14qrexpcl.mm"
include "syl3anc.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "r19.29an.mm"
include "impbida.mm"

theorem pellfund14b
  let vx: setvar x
  let cA: class A
  let cD: class D

  disjoint D x
  disjoint A x
  assert |- ( D e. ( NN \ []NN ) -> ( A e. ( Pell14QR ` D ) <-> E. x e. ZZ A = ( ( PellFund ` D ) ^ x ) ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cA
    cD
    cpellfund
    cfv
    #
    vx
    cv
    #
    cexp
    co
    #
    wceq
    #
    vx
    cz
    wrex
    vx
    cA
    cD
    pellfund14
    @0
    @6
    @2
    vx
    cz
    @0
    @4
    cz
    wcel
    #
    wa
    #
    @6
    wa
    #
    @2
    @5
    @1
    wcel
    #
    @9
    @0
    @3
    @1
    wcel
    #
    @7
    @10
    @0
    @7
    @6
    simpll
    @0
    @11
    @7
    @6
    @0
    cD
    cpell1qr
    cfv
    @1
    @3
    cD
    pell1qrss14
    cD
    pellfundex
    sseldd
    ad2antrr
    @0
    @7
    @6
    simplr
    @3
    @4
    cD
    pell14qrexpcl
    syl3anc
    @6
    @2
    @10
    wb
    @8
    cA
    @5
    @1
    eleq1
    adantl
    mpbird
    r19.29an
    impbida
end
