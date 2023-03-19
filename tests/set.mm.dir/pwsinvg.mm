include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cminusg.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "simp2.mm"
include "fvexd.mm"
include "wf.mm"
include "simp1.mm"
include "fconst6g.mm"
include "syl.mm"
include "simp3.mm"
include "wceq.mm"
include "pwsval.mm"
include "3adant3.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "prdsinvgd.mm"
include "wa.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "pwselbas.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "grpinvf.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"

theorem pwsinvg
  let cB: class B
  let cR: class R
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cF: class F
  assume pwsgrp.y: |- Y = ( R ^s I )
  assume pwsinvg.b: |- B = ( Base ` Y )
  assume pwsinvg.m: |- M = ( invg ` R )
  assume pwsinvg.n: |- N = ( invg ` Y )


  assert |- ( ( R e. Grp /\ I e. V /\ X e. B ) -> ( N ` X ) = ( M o. X ) )

  proof
    cR
    cgrp
    wcel
    #
    cI
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cX
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cminusg
    cfv
    #
    cfv
    #
    vx
    cI
    vx
    cv
    #
    cX
    cfv
    #
    cM
    cfv
    #
    cmpt
    #
    cX
    cN
    cfv
    cM
    cX
    ccom
    @3
    @8
    vx
    cI
    @10
    @9
    @5
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    @12
    @3
    vx
    @6
    cbs
    cfv
    #
    @5
    @4
    cI
    @7
    cvv
    cV
    cX
    @6
    @6
    eqid
    @0
    @1
    @2
    simp2
    #
    @3
    cR
    csca
    fvexd
    @3
    @0
    cI
    cgrp
    @5
    wf
    @0
    @1
    @2
    simp1
    #
    cI
    cR
    cgrp
    fconst6g
    syl
    @16
    eqid
    @7
    eqid
    @3
    cX
    cB
    @16
    @0
    @1
    @2
    simp3
    #
    @3
    cB
    cY
    cbs
    cfv
    @16
    pwsinvg.b
    @3
    cY
    @6
    cbs
    @0
    @1
    cY
    @6
    wceq
    @2
    cR
    @4
    cI
    cgrp
    cV
    cY
    pwsgrp.y
    @4
    eqid
    pwsval
    3adant3
    #
    fveq2d
    syl5eq
    eleqtrd
    prdsinvgd
    @3
    vx
    cI
    @15
    @11
    @3
    @9
    cI
    wcel
    #
    wa
    #
    @10
    @14
    cM
    @22
    @14
    cR
    cminusg
    cfv
    cM
    @22
    @13
    cR
    cminusg
    @3
    @0
    @21
    @13
    cR
    wceq
    @18
    cI
    cR
    @9
    cgrp
    fvconst2g
    sylan
    fveq2d
    pwsinvg.m
    syl6eqr
    fveq1d
    mpteq2dva
    eqtrd
    @3
    cX
    cN
    @7
    @3
    cN
    cY
    cminusg
    cfv
    @7
    pwsinvg.n
    @3
    cY
    @6
    cminusg
    @20
    fveq2d
    syl5eq
    fveq1d
    @3
    vx
    vy
    cI
    cR
    cbs
    cfv
    #
    @10
    vy
    cv
    #
    cM
    cfv
    @11
    cX
    cM
    @3
    cI
    @23
    @9
    cX
    @3
    @23
    cR
    cI
    cB
    cgrp
    cX
    cY
    cV
    pwsgrp.y
    @23
    eqid
    #
    pwsinvg.b
    @18
    @17
    @19
    pwselbas
    #
    ffvelrnda
    @3
    vx
    cI
    @23
    cX
    @26
    feqmptd
    @3
    vy
    @23
    @23
    cM
    @3
    @0
    @23
    @23
    cM
    wf
    @18
    @23
    cR
    cM
    @25
    pwsinvg.m
    grpinvf
    syl
    feqmptd
    @24
    @10
    cM
    fveq2
    fmptco
    3eqtr4d
end
