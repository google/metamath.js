include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "cmulr.mm"
include "co.mm"
include "cmul.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "crg.mm"
include "abvrcl.mm"
include "eqid.mm"
include "isabv.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "simpl.mm"
include "ralimi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem abveq0
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )
  assume abveq0.z: |- .0. = ( 0g ` R )


  assert |- ( ( F e. A /\ X e. B ) -> ( ( F ` X ) = 0 <-> X = .0. ) )

  proof
    cF
    cA
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    @1
    c.0
    wceq
    #
    wb
    #
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    cX
    cF
    cfv
    #
    cc0
    wceq
    #
    cX
    c.0
    wceq
    #
    wb
    #
    @0
    @5
    @1
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    cF
    cfv
    @2
    @11
    cF
    cfv
    #
    cmul
    co
    wceq
    @1
    @11
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    @2
    @13
    caddc
    co
    cle
    wbr
    wa
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    @6
    @0
    cB
    cc0
    cpnf
    cico
    co
    cF
    wf
    #
    @17
    @0
    @18
    @17
    wa
    #
    @0
    cR
    crg
    wcel
    @0
    @19
    wb
    cA
    cR
    cF
    abvf.a
    abvrcl
    vx
    vy
    cA
    cB
    @14
    cR
    @12
    cF
    c.0
    abvf.a
    abvf.b
    @14
    eqid
    @12
    eqid
    abveq0.z
    isabv
    syl
    ibi
    simprd
    @16
    @5
    vx
    cB
    @5
    @15
    simpl
    ralimi
    syl
    @5
    @10
    vx
    cX
    cB
    @1
    cX
    wceq
    #
    @3
    @8
    @4
    @9
    @20
    @2
    @7
    cc0
    @1
    cX
    cF
    fveq2
    eqeq1d
    @1
    cX
    c.0
    eqeq1
    bibi12d
    rspccva
    sylan
end
