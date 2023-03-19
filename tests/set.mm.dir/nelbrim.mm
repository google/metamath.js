include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cnelbr.mm"
include "wbr.mm"
include "wn.mm"
include "wrel.mm"
include "wel.mm"
include "df-nelbr.mm"
include "relopabi.mm"
include "brrelex12.mm"
include "mpan.mm"
include "nelbr.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem nelbrim
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- ( A e// B -> -. A e. B )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    cA
    cB
    cnelbr
    wbr
    #
    cA
    cB
    wcel
    wn
    #
    cnelbr
    wrel
    @1
    @0
    vx
    vy
    wel
    wn
    vx
    vy
    cnelbr
    vx
    vy
    df-nelbr
    relopabi
    cA
    cB
    cnelbr
    brrelex12
    mpan
    @0
    @1
    @2
    cA
    cB
    cvv
    cvv
    nelbr
    biimpd
    mpcom
end
