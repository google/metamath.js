include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cr.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cnghm.mm"
include "cxr.mm"
include "cc0.mm"
include "nmocl.mm"
include "nmoge0.mm"
include "jca.mm"
include "xrrege0.mm"
include "an4s.mm"
include "sylan.mm"
include "wb.mm"
include "isnghm2.mm"
include "adantr.mm"
include "mpbird.mm"

theorem bddnghm
  let cA: class A
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
  let wph: wff ph
  let cV: class V
  let cX: class X
  assume nmofval.1: |- N = ( S normOp T )


  assert |- ( ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) /\ ( A e. RR /\ ( N ` F ) <_ A ) ) -> F e. ( S NGHom T ) )

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
    cA
    cr
    wcel
    #
    cF
    cN
    cfv
    #
    cA
    cle
    wbr
    #
    wa
    #
    wa
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    @2
    cr
    wcel
    #
    @0
    @2
    cxr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @4
    @6
    @0
    @7
    @8
    cS
    cT
    cF
    cN
    nmofval.1
    nmocl
    cS
    cT
    cF
    cN
    nmofval.1
    nmoge0
    jca
    @7
    @1
    @8
    @3
    @6
    @2
    cA
    xrrege0
    an4s
    sylan
    @0
    @5
    @6
    wb
    @4
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm2
    adantr
    mpbird
end
