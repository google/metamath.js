include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "mptctf.mm"
include "rnct.mm"
include "syl.mm"
include "syl5eqbrr.mm"

theorem abrexctf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume mptctf.1: |- F/_ x A

  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A ~<_ _om -> { y | E. x e. A y = B } ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    com
    cdom
    vx
    vy
    cA
    cB
    @1
    @1
    eqid
    rnmpt
    @0
    @1
    com
    cdom
    wbr
    @2
    com
    cdom
    wbr
    vx
    cA
    cB
    mptctf.1
    mptctf
    @1
    rnct
    syl
    syl5eqbrr
end
