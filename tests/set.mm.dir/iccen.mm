include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "ccnv.mm"
include "cdiv.mm"
include "wceq.mm"
include "eqid.mm"
include "iccf1o.mm"
include "simpld.mm"
include "cvv.mm"
include "ovex.mm"
include "f1oen2g.mm"
include "mp3an12.mm"
include "syl.mm"

theorem iccen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR /\ A < B ) -> ( 0 [,] 1 ) ~~ ( A [,] B ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    w3a
    #
    cc0
    c1
    cicc
    co
    #
    cA
    cB
    cicc
    co
    #
    vx
    @1
    vx
    cv
    #
    cB
    cmul
    co
    c1
    @3
    cmin
    co
    cA
    cmul
    co
    caddc
    co
    cmpt
    #
    wf1o
    #
    @1
    @2
    cen
    wbr
    #
    @0
    @5
    @4
    ccnv
    vy
    @2
    vy
    cv
    cA
    cmin
    co
    cB
    cA
    cmin
    co
    cdiv
    co
    cmpt
    wceq
    vx
    vy
    cA
    cB
    @4
    @4
    eqid
    iccf1o
    simpld
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @5
    @6
    cc0
    c1
    cicc
    ovex
    cA
    cB
    cicc
    ovex
    @1
    @2
    @4
    cvv
    cvv
    f1oen2g
    mp3an12
    syl
end
