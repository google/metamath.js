include "cngp.mm"
include "cv.mm"
include "cghm.mm"
include "co.mm"
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
include "cmpt.mm"
include "cnmo.mm"
include "df-nmo.mm"
include "wf.mm"
include "cvv.mm"
include "wcel.mm"
include "eqid.mm"
include "wss.mm"
include "ssrab2.mm"
include "icossxr.mm"
include "sstri.mm"
include "infxrcl.mm"
include "mp1i.mm"
include "fmpti.mm"
include "ovex.mm"
include "xrex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fnmpt2i.mm"

theorem nmoffn
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cL: class L
  let cM: class M
  let cS: class S
  let cT: class T
  let cA: class A
  let cF: class F
  let wph: wff ph
  let cV: class V
  let cX: class X
  let cN: class N


  assert |- normOp Fn ( NrmGrp X. NrmGrp )

  proof
    vs
    vt
    cngp
    cngp
    vf
    vs
    cv
    #
    vt
    cv
    #
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
    @1
    cnm
    cfv
    cfv
    vr
    cv
    @3
    @0
    cnm
    cfv
    cfv
    cmul
    co
    cle
    wbr
    vx
    @0
    cbs
    cfv
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
    cmpt
    #
    cnmo
    vx
    vt
    vf
    vs
    vr
    df-nmo
    @2
    cxr
    @9
    wf
    @2
    cvv
    wcel
    cxr
    cvv
    wcel
    @9
    cvv
    wcel
    vf
    @2
    cxr
    @8
    @9
    @9
    eqid
    @7
    cxr
    wss
    @8
    cxr
    wcel
    @4
    @2
    wcel
    @7
    @6
    cxr
    @5
    vr
    @6
    ssrab2
    cc0
    cpnf
    icossxr
    sstri
    @7
    infxrcl
    mp1i
    fmpti
    @0
    @1
    cghm
    ovex
    xrex
    @2
    cxr
    @9
    cvv
    cvv
    fex2
    mp3an
    fnmpt2i
end
