include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cdm.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "mvmulfval.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wral.mm"
include "wceq.mm"
include "wa.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "dmmpt2ga.mm"
include "syl.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqcomd.mm"
include "xpeq12d.mm"
include "3eqtrd.mm"

theorem mavmuldm
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  assume mavmuldm.b: |- B = ( Base ` R )
  assume mavmuldm.c: |- C = ( B ^m ( M X. N ) )
  assume mavmuldm.d: |- D = ( B ^m N )
  assume mavmuldm.t: |- .x. = ( R maVecMul <. M , N >. )


  assert |- ( ( R e. V /\ M e. Fin /\ N e. Fin ) -> dom .x. = ( C X. D ) )

  proof
    cR
    cV
    wcel
    #
    cM
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    w3a
    #
    c.x
    cdm
    vx
    vy
    cB
    cM
    cN
    cxp
    cmap
    co
    #
    cB
    cN
    cmap
    co
    #
    vi
    cM
    cR
    vj
    cN
    vi
    cv
    vj
    cv
    #
    vx
    cv
    #
    co
    @6
    vy
    cv
    #
    cfv
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    #
    cdm
    #
    @4
    @5
    cxp
    #
    cC
    cD
    cxp
    @3
    c.x
    @12
    @3
    vx
    vy
    cB
    cR
    @9
    c.x
    vi
    vj
    cM
    cN
    cV
    mavmuldm.t
    mavmuldm.b
    @9
    eqid
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    mvmulfval
    dmeqd
    @3
    @11
    cvv
    wcel
    #
    vy
    @5
    wral
    vx
    @4
    wral
    @13
    @14
    wceq
    @3
    @15
    vx
    vy
    @4
    @5
    @3
    @15
    @7
    @4
    wcel
    @8
    @5
    wcel
    wa
    @1
    @0
    @15
    @2
    vi
    cM
    @10
    cfn
    mptexg
    3ad2ant2
    a1d
    ralrimivv
    vx
    vy
    @4
    @5
    @11
    @12
    cvv
    @12
    eqid
    dmmpt2ga
    syl
    @3
    @4
    cC
    @5
    cD
    @4
    cC
    wceq
    @3
    cC
    @4
    mavmuldm.c
    eqcomi
    a1i
    @3
    cD
    @5
    cD
    @5
    wceq
    @3
    mavmuldm.d
    a1i
    eqcomd
    xpeq12d
    3eqtrd
end
