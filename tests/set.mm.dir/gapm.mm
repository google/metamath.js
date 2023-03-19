include "cga.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cminusg.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "gaf.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "fovrnd.mm"
include "cgrp.mm"
include "gagrp.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wb.mm"
include "simpll.mm"
include "simprl.mm"
include "simprr.mm"
include "gacan.mm"
include "syl13anc.mm"
include "bicomd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "f1o2d.mm"

theorem gapm
  let vx: setvar x
  let cA: class A
  let c.po: class .(+)
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume gapm.1: |- X = ( Base ` G )
  assume gapm.2: |- F = ( x e. Y |-> ( A .(+) x ) )

  disjoint A x
  disjoint G x
  disjoint .(+) x
  disjoint X x
  disjoint Y x
  disjoint x y
  disjoint A y
  disjoint G y
  disjoint .(+) y
  disjoint X y
  disjoint Y y
  assert |- ( ( .(+) e. ( G GrpAct Y ) /\ A e. X ) -> F : Y -1-1-onto-> Y )

  proof
    c.po
    cG
    cY
    cga
    co
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vx
    vy
    cY
    cY
    cA
    vx
    cv
    #
    c.po
    co
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    vy
    cv
    #
    c.po
    co
    #
    cF
    gapm.2
    @2
    @3
    cY
    wcel
    #
    wa
    cA
    @3
    cY
    cX
    cY
    c.po
    @0
    cX
    cY
    cxp
    cY
    c.po
    wf
    #
    @1
    @9
    c.po
    cG
    cX
    cY
    gapm.1
    gaf
    #
    ad2antrr
    @0
    @1
    @9
    simplr
    @2
    @9
    simpr
    fovrnd
    @2
    @7
    cY
    wcel
    #
    wa
    #
    @6
    @7
    cY
    cX
    cY
    c.po
    @0
    @10
    @1
    @12
    @11
    ad2antrr
    @13
    cG
    cgrp
    wcel
    #
    @1
    @6
    cX
    wcel
    @0
    @14
    @1
    @12
    c.po
    cG
    cY
    gagrp
    ad2antrr
    @0
    @1
    @12
    simplr
    cX
    cG
    @5
    cA
    gapm.1
    @5
    eqid
    #
    grpinvcl
    syl2anc
    @2
    @12
    simpr
    fovrnd
    @2
    @9
    @12
    wa
    #
    wa
    #
    @8
    @3
    wceq
    #
    @4
    @7
    wceq
    #
    @3
    @8
    wceq
    @7
    @4
    wceq
    @17
    @19
    @18
    @17
    @0
    @1
    @9
    @12
    @19
    @18
    wb
    @0
    @1
    @16
    simpll
    @0
    @1
    @16
    simplr
    @2
    @9
    @12
    simprl
    @2
    @9
    @12
    simprr
    cA
    @3
    @7
    c.po
    cG
    @5
    cX
    cY
    gapm.1
    @15
    gacan
    syl13anc
    bicomd
    @3
    @8
    eqcom
    @7
    @4
    eqcom
    3bitr4g
    f1o2d
end
