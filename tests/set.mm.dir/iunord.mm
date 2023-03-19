include "word.mm"
include "wral.mm"
include "ciun.mm"
include "wtr.mm"
include "con0.mm"
include "wss.mm"
include "ordtr.mm"
include "ralimi.mm"
include "triun.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "eliun.mm"
include "nfra1.mm"
include "nfv.mm"
include "wi.mm"
include "rsp.mm"
include "ordelon.mm"
include "ex.mm"
include "syl6.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ordon.mm"
include "trssord.mm"
include "3exp.mm"
include "mpii.mm"
include "sylc.mm"

theorem iunord
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint k x
  assert |- ( A. x e. A Ord B -> Ord U_ x e. A B )

  proof
    cB
    word
    #
    vx
    cA
    wral
    #
    vx
    cA
    cB
    ciun
    #
    wtr
    #
    @2
    con0
    wss
    #
    @2
    word
    #
    @1
    cB
    wtr
    #
    vx
    cA
    wral
    @3
    @0
    @6
    vx
    cA
    cB
    ordtr
    ralimi
    vx
    cA
    cB
    triun
    syl
    @1
    vy
    @2
    con0
    vy
    cv
    #
    @2
    wcel
    @7
    cB
    wcel
    #
    vx
    cA
    wrex
    @1
    @7
    con0
    wcel
    #
    vx
    @7
    cA
    cB
    eliun
    @1
    @8
    @9
    vx
    cA
    @0
    vx
    cA
    nfra1
    @9
    vx
    nfv
    @1
    vx
    cv
    cA
    wcel
    @0
    @8
    @9
    wi
    @0
    vx
    cA
    rsp
    @0
    @8
    @9
    cB
    @7
    ordelon
    ex
    syl6
    rexlimd
    syl5bi
    ssrdv
    @3
    @4
    con0
    word
    #
    @5
    ordon
    @3
    @4
    @10
    @5
    @2
    con0
    trssord
    3exp
    mpii
    sylc
end
