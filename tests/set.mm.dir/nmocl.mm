include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "cfv.mm"
include "cxr.mm"
include "wa.mm"
include "nmof.mm"
include "ffvelrnda.mm"
include "3impa.mm"

theorem nmocl
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


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> ( N ` F ) e. RR* )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    cF
    cN
    cfv
    cxr
    wcel
    @0
    @1
    wa
    @2
    cxr
    cF
    cN
    cS
    cT
    cN
    nmofval.1
    nmof
    ffvelrnda
    3impa
end
