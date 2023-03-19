include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cnm.mm"
include "cmul.mm"
include "cbs.mm"
include "wral.mm"
include "wi.mm"
include "cpnf.mm"
include "cico.mm"
include "wa.mm"
include "cr.mm"
include "elrege0.mm"
include "simprbi.mm"
include "adantl.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "wb.mm"
include "0xr.mm"
include "eqid.mm"
include "nmogelb.mm"
include "mpan2.mm"
include "mpbird.mm"

theorem nmoge0
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cL: class L
  let cM: class M
  let cA: class A
  let wph: wff ph
  let cV: class V
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> 0 <_ ( N ` F ) )

  proof
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    cF
    cS
    cT
    cghm
    co
    wcel
    w3a
    #
    cc0
    cF
    cN
    cfv
    cle
    wbr
    #
    vx
    cv
    #
    cF
    cfv
    cT
    cnm
    cfv
    #
    cfv
    vr
    cv
    #
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
    cc0
    @4
    cle
    wbr
    #
    wi
    #
    vr
    cc0
    cpnf
    cico
    co
    #
    wral
    #
    @0
    @9
    vr
    @10
    @0
    @4
    @10
    wcel
    #
    wa
    @8
    @7
    @12
    @8
    @0
    @12
    @4
    cr
    wcel
    @8
    @4
    elrege0
    simprbi
    adantl
    a1d
    ralrimiva
    @0
    cc0
    cxr
    wcel
    @1
    @11
    wb
    0xr
    vx
    cc0
    cS
    cT
    cF
    @5
    @3
    cN
    @6
    vr
    nmofval.1
    @6
    eqid
    @5
    eqid
    @3
    eqid
    nmogelb
    mpan2
    mpbird
end
