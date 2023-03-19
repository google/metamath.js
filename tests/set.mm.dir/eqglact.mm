include "cgrp.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "cminusg.mm"
include "cfv.mm"
include "co.mm"
include "wa.mm"
include "cec.mm"
include "cmpt.mm"
include "cima.mm"
include "wb.mm"
include "eqid.mm"
include "eqgval.mm"
include "3anass.mm"
include "syl6bb.mm"
include "baibd.mm"
include "3impa.mm"
include "abbidv.mm"
include "wceq.mm"
include "dfec2.mm"
include "3ad2ant3.mm"
include "ccnv.mm"
include "wf1o.mm"
include "grplactcnv.mm"
include "simprd.mm"
include "grplactfval.mm"
include "adantl.mm"
include "cnveqd.mm"
include "grpinvcl.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "3adant2.mm"
include "imaeq1d.mm"
include "imacnvcnv.mm"
include "crab.mm"
include "mptpreima.mm"
include "df-rab.mm"
include "eqtri.mm"
include "3eqtr3g.mm"
include "3eqtr4d.mm"

theorem eqglact
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let c.sm: class .~
  let cG: class G
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  assume eqger.x: |- X = ( Base ` G )
  assume eqger.r: |- .~ = ( G ~QG Y )
  assume eqglact.3: |- .+ = ( +g ` G )

  disjoint .+ x
  disjoint .~ x
  disjoint G x
  disjoint X x
  disjoint A x
  disjoint Y x
  disjoint g x
  disjoint .+ g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint .~ y
  disjoint .~ z
  disjoint .0. x
  disjoint g y
  disjoint g z
  disjoint G g
  disjoint G y
  disjoint G z
  disjoint X g
  disjoint X y
  disjoint X z
  disjoint A g
  disjoint Y y
  disjoint Y z
  assert |- ( ( G e. Grp /\ Y C_ X /\ A e. X ) -> [ A ] .~ = ( ( x e. X |-> ( A .+ x ) ) " Y ) )

  proof
    cG
    cgrp
    wcel
    #
    cY
    cX
    wss
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cA
    vx
    cv
    #
    c.sm
    wbr
    #
    vx
    cab
    #
    @4
    cX
    wcel
    #
    cA
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    c.pl
    co
    #
    cY
    wcel
    #
    wa
    #
    vx
    cab
    #
    cA
    c.sm
    cec
    #
    vx
    cX
    cA
    @4
    c.pl
    co
    cmpt
    #
    cY
    cima
    #
    @3
    @5
    @12
    vx
    @0
    @1
    @2
    @5
    @12
    wb
    @0
    @1
    wa
    #
    @5
    @2
    @12
    @17
    @5
    @2
    @7
    @11
    w3a
    @2
    @12
    wa
    cA
    @4
    c.pl
    c.sm
    cY
    cG
    @8
    cgrp
    cX
    eqger.x
    @8
    eqid
    #
    eqglact.3
    eqger.r
    eqgval
    @2
    @7
    @11
    3anass
    syl6bb
    baibd
    3impa
    abbidv
    @2
    @0
    @14
    @6
    wceq
    @1
    vx
    cA
    c.sm
    cX
    dfec2
    3ad2ant3
    @3
    @15
    ccnv
    #
    ccnv
    #
    cY
    cima
    vx
    cX
    @10
    cmpt
    #
    ccnv
    #
    cY
    cima
    #
    @16
    @13
    @3
    @20
    @22
    cY
    @0
    @2
    @20
    @22
    wceq
    @1
    @0
    @2
    wa
    #
    @19
    @21
    @24
    cA
    vg
    cX
    vx
    cX
    vg
    cv
    @4
    c.pl
    co
    cmpt
    cmpt
    #
    cfv
    #
    ccnv
    #
    @9
    @25
    cfv
    #
    @19
    @21
    @24
    cX
    cX
    @26
    wf1o
    @27
    @28
    wceq
    cA
    c.pl
    vg
    @25
    cG
    @8
    cX
    vx
    @25
    eqid
    #
    eqger.x
    eqglact.3
    @18
    grplactcnv
    simprd
    @24
    @26
    @15
    @2
    @26
    @15
    wceq
    @0
    cA
    c.pl
    vg
    @25
    cG
    cX
    vx
    @29
    eqger.x
    grplactfval
    adantl
    cnveqd
    @24
    @9
    cX
    wcel
    @28
    @21
    wceq
    cX
    cG
    @8
    cA
    eqger.x
    @18
    grpinvcl
    @9
    c.pl
    vg
    @25
    cG
    cX
    vx
    @29
    eqger.x
    grplactfval
    syl
    3eqtr3d
    cnveqd
    3adant2
    imaeq1d
    @15
    cY
    imacnvcnv
    @23
    @11
    vx
    cX
    crab
    @13
    vx
    cX
    @10
    cY
    @21
    @21
    eqid
    mptpreima
    @11
    vx
    cX
    df-rab
    eqtri
    3eqtr3g
    3eqtr4d
end
