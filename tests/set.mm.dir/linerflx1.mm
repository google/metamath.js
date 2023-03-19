include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "crab.mm"
include "cline2.mm"
include "co.mm"
include "simpr1.mm"
include "colineartriv1.mm"
include "3adant3r3.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "fvline2.mm"
include "eleqtrrd.mm"

theorem linerflx1
  let cP: class P
  let cQ: class Q
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) -> P e. ( P Line Q ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    wa
    #
    cP
    vx
    cv
    #
    cP
    cQ
    cop
    #
    ccolin
    wbr
    #
    vx
    @1
    crab
    #
    cP
    cQ
    cline2
    co
    @5
    @2
    cP
    @7
    ccolin
    wbr
    #
    cP
    @9
    wcel
    @0
    @2
    @3
    @4
    simpr1
    @0
    @2
    @3
    @10
    @4
    cP
    cQ
    cN
    colineartriv1
    3adant3r3
    @8
    @10
    vx
    cP
    @1
    @6
    cP
    @7
    ccolin
    breq1
    elrab
    sylanbrc
    vx
    cP
    cQ
    cN
    fvline2
    eleqtrrd
end
