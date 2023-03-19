include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "c0g.mm"
include "wb.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
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
include "adantl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem abvmul
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )
  assume abvmul.t: |- .x. = ( .r ` R )


  assert |- ( ( F e. A /\ X e. B /\ Y e. B ) -> ( F ` ( X .x. Y ) ) = ( ( F ` X ) x. ( F ` Y ) ) )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.x
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cmul
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @8
    @0
    @13
    cc0
    wceq
    @9
    cR
    c0g
    cfv
    #
    wceq
    wb
    #
    @16
    @9
    @10
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    @13
    @14
    caddc
    co
    cle
    wbr
    #
    wa
    #
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
    @18
    @0
    cB
    cc0
    cpnf
    cico
    co
    cF
    wf
    #
    @26
    @0
    @27
    @26
    wa
    #
    @0
    cR
    crg
    wcel
    @0
    @28
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
    @21
    cR
    c.x
    cF
    @19
    abvf.a
    abvf.b
    @21
    eqid
    abvmul.t
    @19
    eqid
    isabv
    syl
    ibi
    simprd
    @25
    @17
    vx
    cB
    @24
    @17
    @20
    @23
    @16
    vy
    cB
    @16
    @22
    simpl
    ralimi
    adantl
    ralimi
    syl
    @16
    @8
    cX
    @10
    c.x
    co
    #
    cF
    cfv
    #
    @5
    @14
    cmul
    co
    #
    wceq
    vx
    vy
    cX
    cY
    cB
    cB
    @9
    cX
    wceq
    #
    @12
    @30
    @15
    @31
    @32
    @11
    @29
    cF
    @9
    cX
    @10
    c.x
    oveq1
    fveq2d
    @32
    @13
    @5
    @14
    cmul
    @9
    cX
    cF
    fveq2
    oveq1d
    eqeq12d
    @10
    cY
    wceq
    #
    @30
    @4
    @31
    @7
    @33
    @29
    @3
    cF
    @10
    cY
    cX
    c.x
    oveq2
    fveq2d
    @33
    @14
    @6
    @5
    cmul
    @10
    cY
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl5com
    3impib
end
