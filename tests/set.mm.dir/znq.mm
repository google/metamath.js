include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cq.mm"
include "eqid.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "elq.mm"
include "sylibr.mm"

theorem znq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A / B ) e. QQ )

  proof
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    cA
    cB
    cdiv
    co
    #
    vx
    cv
    vy
    cv
    cdiv
    co
    wceq
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    @2
    cq
    wcel
    @0
    @1
    @2
    @2
    wceq
    @3
    @2
    eqid
    vx
    vy
    cz
    cn
    cA
    cB
    @2
    cdiv
    rspceov
    mp3an3
    vx
    vy
    @2
    elq
    sylibr
end
