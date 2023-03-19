include "wne.mm"
include "cc0.mm"
include "c3.mm"
include "cop.mm"
include "c1.mm"
include "c6.mm"
include "cpr.mm"
include "c2.mm"
include "c4.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "opex.mm"
include "pm3.2i.mm"
include "2re.mm"
include "2lt3.mm"
include "gtneii.mm"
include "olci.mm"
include "c0ex.mm"
include "3ex.mm"
include "opthne.mm"
include "mpbir.mm"
include "0ne1.mm"
include "orci.mm"
include "prneimg.mm"
include "mp2.mm"
include "neeq12i.mm"

theorem zlmodzxzldeplem
  let cA: class A
  let cB: class B
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume zlmodzxzldep.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzldep.a: |- A = { <. 0 , 3 >. , <. 1 , 6 >. }
  assume zlmodzxzldep.b: |- B = { <. 0 , 2 >. , <. 1 , 4 >. }


  assert |- A =/= B

  proof
    cA
    cB
    wne
    cc0
    c3
    cop
    #
    c1
    c6
    cop
    #
    cpr
    #
    cc0
    c2
    cop
    #
    c1
    c4
    cop
    #
    cpr
    #
    wne
    #
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    #
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    wa
    #
    wa
    @0
    @3
    wne
    #
    @0
    @4
    wne
    #
    wa
    #
    @1
    @3
    wne
    @1
    @4
    wne
    wa
    #
    wo
    @6
    @9
    @12
    @7
    @8
    cc0
    c3
    opex
    c1
    c6
    opex
    pm3.2i
    @10
    @11
    cc0
    c2
    opex
    c1
    c4
    opex
    pm3.2i
    pm3.2i
    @15
    @16
    @13
    @14
    @13
    cc0
    cc0
    wne
    #
    c3
    c2
    wne
    #
    wo
    @18
    @17
    c2
    c3
    2re
    2lt3
    gtneii
    olci
    cc0
    c3
    cc0
    c2
    c0ex
    3ex
    opthne
    mpbir
    @14
    cc0
    c1
    wne
    #
    c3
    c4
    wne
    #
    wo
    @19
    @20
    0ne1
    orci
    cc0
    c3
    c1
    c4
    c0ex
    3ex
    opthne
    mpbir
    pm3.2i
    orci
    @0
    @1
    @3
    @4
    cvv
    cvv
    cvv
    cvv
    prneimg
    mp2
    cA
    @2
    cB
    @5
    zlmodzxzldep.a
    zlmodzxzldep.b
    neeq12i
    mpbir
end
