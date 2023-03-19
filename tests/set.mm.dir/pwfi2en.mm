include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "eqid.mm"
include "pwfi2f1o.mm"
include "c0.mm"
include "cfsupp.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "ovex.mm"
include "rabex2.mm"
include "f1oen.mm"
include "syl.mm"

theorem pwfi2en
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cV: class V
  let vx: setvar x
  assume pwfi2en.s: |- S = { y e. ( 2o ^m A ) | y finSupp (/) }

  disjoint A y
  disjoint V y
  disjoint x y
  disjoint A x
  disjoint S x
  disjoint V x
  assert |- ( A e. V -> S ~~ ( ~P A i^i Fin ) )

  proof
    cA
    cV
    wcel
    cS
    cA
    cpw
    cfn
    cin
    #
    vx
    cS
    vx
    cv
    ccnv
    c1o
    csn
    cima
    cmpt
    #
    wf1o
    cS
    @0
    cen
    wbr
    vx
    vy
    cA
    cS
    @1
    cV
    pwfi2en.s
    @1
    eqid
    pwfi2f1o
    cS
    @0
    @1
    vy
    cv
    c0
    cfsupp
    wbr
    vy
    c2o
    cA
    cmap
    co
    cS
    pwfi2en.s
    c2o
    cA
    cmap
    ovex
    rabex2
    f1oen
    syl
end
