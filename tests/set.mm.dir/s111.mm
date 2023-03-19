include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "wceq.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "s1val.mm"
include "eqeqan12d.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "sneqbg.mm"
include "mp1i.mm"
include "cz.mm"
include "0z.mm"
include "eqid.mm"
include "opthg.mm"
include "baibd.mm"
include "mpan2.mm"
include "mpan.mm"
include "adantr.mm"
include "3bitrd.mm"

theorem s111
  let cA: class A
  let cS: class S
  let cT: class T


  assert |- ( ( S e. A /\ T e. A ) -> ( <" S "> = <" T "> <-> S = T ) )

  proof
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    wa
    #
    cS
    cs1
    #
    cT
    cs1
    #
    wceq
    cc0
    cS
    cop
    #
    csn
    #
    cc0
    cT
    cop
    #
    csn
    #
    wceq
    #
    @5
    @7
    wceq
    #
    cS
    cT
    wceq
    #
    @0
    @1
    @3
    @6
    @4
    @8
    cS
    cA
    s1val
    cT
    cA
    s1val
    eqeqan12d
    @5
    cvv
    wcel
    @9
    @10
    wb
    @2
    cc0
    cS
    opex
    @5
    @7
    cvv
    sneqbg
    mp1i
    @0
    @10
    @11
    wb
    #
    @1
    cc0
    cz
    wcel
    #
    @0
    @12
    0z
    @13
    @0
    wa
    #
    cc0
    cc0
    wceq
    #
    @12
    cc0
    eqid
    @14
    @10
    @15
    @11
    cc0
    cS
    cc0
    cT
    cz
    cA
    opthg
    baibd
    mpan2
    mpan
    adantr
    3bitrd
end
