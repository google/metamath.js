include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "cnghm.mm"
include "cfv.mm"
include "cr.mm"
include "wb.mm"
include "wa.mm"
include "isnghm.mm"
include "baib.mm"
include "baibd.mm"
include "3impa.mm"

theorem isnghm2
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


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> ( F e. ( S NGHom T ) <-> ( N ` F ) e. RR ) )

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
    wcel
    #
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cF
    cN
    cfv
    cr
    wcel
    #
    wb
    @0
    @1
    wa
    #
    @3
    @2
    @4
    @3
    @5
    @2
    @4
    wa
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm
    baib
    baibd
    3impa
end
