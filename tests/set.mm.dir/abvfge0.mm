include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "wb.mm"
include "cmulr.mm"
include "cmul.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "crg.mm"
include "abvrcl.mm"
include "eqid.mm"
include "isabv.mm"
include "syl.mm"
include "ibi.mm"
include "simpld.mm"

theorem abvfge0
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  let cX: class X
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )


  assert |- ( F e. A -> F : B --> ( 0 [,) +oo ) )

  proof
    cF
    cA
    wcel
    #
    cB
    cc0
    cpnf
    cico
    co
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    @2
    cR
    c0g
    cfv
    #
    wceq
    wb
    @2
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
    @3
    @5
    cF
    cfv
    #
    cmul
    co
    wceq
    @2
    @5
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    @3
    @7
    caddc
    co
    cle
    wbr
    wa
    vy
    cB
    wral
    wa
    vx
    cB
    wral
    #
    @0
    @1
    @9
    wa
    #
    @0
    cR
    crg
    wcel
    @0
    @10
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
    @8
    cR
    @6
    cF
    @4
    abvf.a
    abvf.b
    @8
    eqid
    @6
    eqid
    @4
    eqid
    isabv
    syl
    ibi
    simpld
end
