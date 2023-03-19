include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "cif.mm"
include "cmpt.mm"
include "mptun.mm"
include "inundif.mm"
include "eqid.mm"
include "mpteq12i.mm"
include "elinel2.mm"
include "iftrued.mm"
include "mpteq2ia.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "uneq12i.mm"
include "3eqtr3i.mm"

theorem partfun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( x e. A |-> if ( x e. B , C , D ) ) = ( ( x e. ( A i^i B ) |-> C ) u. ( x e. ( A \ B ) |-> D ) )

  proof
    vx
    cA
    cB
    cin
    #
    cA
    cB
    cdif
    #
    cun
    #
    vx
    cv
    #
    cB
    wcel
    #
    cC
    cD
    cif
    #
    cmpt
    vx
    @0
    @5
    cmpt
    #
    vx
    @1
    @5
    cmpt
    #
    cun
    vx
    cA
    @5
    cmpt
    vx
    @0
    cC
    cmpt
    #
    vx
    @1
    cD
    cmpt
    #
    cun
    vx
    @0
    @1
    @5
    mptun
    vx
    @2
    @5
    cA
    @5
    cA
    cB
    inundif
    @5
    eqid
    mpteq12i
    @6
    @8
    @7
    @9
    vx
    @0
    @5
    cC
    @3
    @0
    wcel
    @4
    cC
    cD
    @3
    cA
    cB
    elinel2
    iftrued
    mpteq2ia
    vx
    @1
    @5
    cD
    @3
    @1
    wcel
    @4
    cC
    cD
    @3
    cA
    cB
    eldifn
    iffalsed
    mpteq2ia
    uneq12i
    3eqtr3i
end
