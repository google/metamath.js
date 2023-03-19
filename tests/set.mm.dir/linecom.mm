include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "crab.mm"
include "cline2.mm"
include "co.mm"
include "wb.mm"
include "simp1.mm"
include "simp3.mm"
include "simp21.mm"
include "simp22.mm"
include "colinearperm1.mm"
include "syl13anc.mm"
include "3expa.mm"
include "rabbidva.mm"
include "fvline2.mm"
include "wceq.mm"
include "necom.mm"
include "3anbi3i.mm"
include "3ancoma.mm"
include "bitri.mm"
include "sylan2b.mm"
include "3eqtr4d.mm"

theorem linecom
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) -> ( P Line Q ) = ( Q Line P ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    wa
    #
    vx
    cv
    #
    cP
    cQ
    cop
    ccolin
    wbr
    #
    vx
    @1
    crab
    @7
    cQ
    cP
    cop
    ccolin
    wbr
    #
    vx
    @1
    crab
    #
    cP
    cQ
    cline2
    co
    cQ
    cP
    cline2
    co
    #
    @6
    @8
    @9
    vx
    @1
    @0
    @5
    @7
    @1
    wcel
    #
    @8
    @9
    wb
    #
    @0
    @5
    @12
    w3a
    @0
    @12
    @2
    @3
    @13
    @0
    @5
    @12
    simp1
    @0
    @5
    @12
    simp3
    @0
    @2
    @3
    @4
    @12
    simp21
    @0
    @2
    @3
    @4
    @12
    simp22
    @7
    cP
    cQ
    cN
    colinearperm1
    syl13anc
    3expa
    rabbidva
    vx
    cP
    cQ
    cN
    fvline2
    @5
    @0
    @3
    @2
    cQ
    cP
    wne
    #
    w3a
    #
    @11
    @10
    wceq
    @5
    @2
    @3
    @14
    w3a
    @15
    @4
    @14
    @2
    @3
    cP
    cQ
    necom
    3anbi3i
    @2
    @3
    @14
    3ancoma
    bitri
    vx
    cQ
    cP
    cN
    fvline2
    sylan2b
    3eqtr4d
end
