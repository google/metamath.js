include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "id.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "2z.mm"
include "a1i.mm"
include "zmulcld.mm"
include "peano2zd.mm"
include "odd2np1.mm"
include "syl.mm"
include "mpbird.mm"
include "adantr.mm"
include "breq2.mm"
include "mtbird.mm"

theorem 2tp1odd
  let cA: class A
  let cB: class B
  let vk: setvar k


  assert |- ( ( A e. ZZ /\ B = ( ( 2 x. A ) + 1 ) ) -> -. 2 || B )

  proof
    cA
    cz
    wcel
    #
    cB
    c2
    cA
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    wa
    c2
    cB
    cdvds
    wbr
    #
    c2
    @2
    cdvds
    wbr
    #
    @0
    @5
    wn
    #
    @3
    @0
    @6
    c2
    vk
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @2
    wceq
    #
    vk
    cz
    wrex
    #
    @0
    @10
    @2
    @2
    wceq
    #
    vk
    cA
    cz
    @0
    id
    #
    @7
    cA
    wceq
    #
    @10
    @12
    wb
    @0
    @14
    @9
    @2
    @2
    @14
    @8
    @1
    c1
    caddc
    @7
    cA
    c2
    cmul
    oveq2
    oveq1d
    eqeq1d
    adantl
    @0
    @2
    eqidd
    rspcedvd
    @0
    @2
    cz
    wcel
    @6
    @11
    wb
    @0
    @1
    @0
    c2
    cA
    c2
    cz
    wcel
    @0
    2z
    a1i
    @13
    zmulcld
    peano2zd
    vk
    @2
    odd2np1
    syl
    mpbird
    adantr
    @3
    @4
    @5
    wb
    @0
    cB
    @2
    c2
    cdvds
    breq2
    adantl
    mtbird
end
