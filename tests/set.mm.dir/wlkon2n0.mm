include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wne.mm"
include "chash.mm"
include "cc0.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "cwlks.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "eqid.mm"
include "wlkonprop.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "eqtr2.mm"
include "nne.mm"
include "sylibr.mm"
include "syl6bi.mm"
include "com12.mm"
include "3adant1.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "necon2ad.mm"
include "imp.mm"

theorem wlkon2n0
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( A ( WalksOn ` G ) B ) P /\ A =/= B ) -> ( # ` F ) =/= 0 )

  proof
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cA
    cB
    wne
    #
    cF
    chash
    cfv
    #
    cc0
    wne
    @0
    @1
    @2
    cc0
    @0
    cG
    cvv
    wcel
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @3
    wcel
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    @2
    cP
    cfv
    #
    cB
    wceq
    #
    w3a
    #
    w3a
    @2
    cc0
    wceq
    #
    @1
    wn
    #
    wi
    #
    cA
    cB
    cP
    cF
    cG
    @3
    @3
    eqid
    wlkonprop
    @11
    @4
    @14
    @5
    @8
    @10
    @14
    @6
    @12
    @8
    @10
    wa
    #
    @13
    @12
    @15
    @8
    @7
    cB
    wceq
    #
    wa
    #
    @13
    @12
    @10
    @16
    @8
    @12
    @9
    @7
    cB
    @2
    cc0
    cP
    fveq2
    eqeq1d
    anbi2d
    @17
    cA
    cB
    wceq
    @13
    @7
    cA
    cB
    eqtr2
    cA
    cB
    nne
    sylibr
    syl6bi
    com12
    3adant1
    3ad2ant3
    syl
    necon2ad
    imp
end
