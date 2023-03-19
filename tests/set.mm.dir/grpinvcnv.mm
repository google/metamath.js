include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wceq.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "wa.mm"
include "wb.mm"
include "w3a.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "grpinvid1.mm"
include "3com23.mm"
include "grpinvid2.mm"
include "bitr4d.mm"
include "3expb.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1ocnv2d.mm"
include "simprd.mm"
include "grpinvf.mm"
include "feqmptd.mm"
include "cnveqd.mm"
include "3eqtr4d.mm"

theorem grpinvcnv
  let cB: class B
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume grpinvinv.b: |- B = ( Base ` G )
  assume grpinvinv.n: |- N = ( invg ` G )


  assert |- ( G e. Grp -> `' N = N )

  proof
    cG
    cgrp
    wcel
    #
    vx
    cB
    vx
    cv
    #
    cN
    cfv
    #
    cmpt
    #
    ccnv
    #
    vy
    cB
    vy
    cv
    #
    cN
    cfv
    #
    cmpt
    #
    cN
    ccnv
    cN
    @0
    cB
    cB
    @3
    wf1o
    @4
    @7
    wceq
    @0
    vx
    vy
    cB
    cB
    @2
    @6
    @3
    @3
    eqid
    cB
    cG
    cN
    @1
    grpinvinv.b
    grpinvinv.n
    grpinvcl
    cB
    cG
    cN
    @5
    grpinvinv.b
    grpinvinv.n
    grpinvcl
    @0
    @1
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    wa
    @6
    @1
    wceq
    #
    @2
    @5
    wceq
    #
    @1
    @6
    wceq
    @5
    @2
    wceq
    @0
    @8
    @9
    @10
    @11
    wb
    @0
    @8
    @9
    w3a
    @10
    @5
    @1
    cG
    cplusg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    @11
    @0
    @9
    @8
    @10
    @14
    wb
    cB
    @12
    cG
    cN
    @5
    @1
    @13
    grpinvinv.b
    @12
    eqid
    #
    @13
    eqid
    #
    grpinvinv.n
    grpinvid1
    3com23
    cB
    @12
    cG
    cN
    @1
    @5
    @13
    grpinvinv.b
    @15
    @16
    grpinvinv.n
    grpinvid2
    bitr4d
    3expb
    @1
    @6
    eqcom
    @5
    @2
    eqcom
    3bitr4g
    f1ocnv2d
    simprd
    @0
    cN
    @3
    @0
    vx
    cB
    cB
    cN
    cB
    cG
    cN
    grpinvinv.b
    grpinvinv.n
    grpinvf
    #
    feqmptd
    cnveqd
    @0
    vy
    cB
    cB
    cN
    @17
    feqmptd
    3eqtr4d
end
