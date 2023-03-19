include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cnm.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cbs.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "eqid.mm"
include "nmofval.mm"
include "wss.mm"
include "ssrab2.mm"
include "icossxr.mm"
include "sstri.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "fmpt3d.mm"

theorem nmof
  let cS: class S
  let cT: class T
  let cN: class N
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cL: class L
  let cM: class M
  let cA: class A
  let cF: class F
  let wph: wff ph
  let cV: class V
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp ) -> N : ( S GrpHom T ) --> RR* )

  proof
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
    #
    vf
    cS
    cT
    cghm
    co
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    cT
    cnm
    cfv
    #
    cfv
    vr
    cv
    @2
    cS
    cnm
    cfv
    #
    cfv
    cmul
    co
    cle
    wbr
    vx
    cS
    cbs
    cfv
    #
    wral
    #
    vr
    cc0
    cpnf
    cico
    co
    #
    crab
    #
    cxr
    clt
    cinf
    #
    cxr
    cN
    vx
    cS
    cT
    vf
    @5
    @4
    cN
    @6
    vr
    nmofval.1
    @6
    eqid
    @5
    eqid
    @4
    eqid
    nmofval
    @9
    cxr
    wss
    @10
    cxr
    wcel
    @0
    @3
    @1
    wcel
    wa
    @9
    @8
    cxr
    @7
    vr
    @8
    ssrab2
    cc0
    cpnf
    icossxr
    sstri
    @9
    infxrcl
    mp1i
    fmpt3d
end
