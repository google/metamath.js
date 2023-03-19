include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cnghm.mm"
include "cfv.mm"
include "cr.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "isnghm2.mm"
include "cxr.mm"
include "cmnf.mm"
include "wb.mm"
include "nmocl.mm"
include "cc0.mm"
include "cle.mm"
include "nmoge0.mm"
include "ge0gtmnf.mm"
include "syl2anc.mm"
include "xrrebnd.mm"
include "baibd.mm"
include "bitrd.mm"

theorem isnghm3
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


  assert |- ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) -> ( F e. ( S NGHom T ) <-> ( N ` F ) < +oo ) )

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
    cF
    cS
    cT
    cnghm
    co
    wcel
    cF
    cN
    cfv
    #
    cr
    wcel
    #
    @1
    cpnf
    clt
    wbr
    #
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm2
    @0
    @1
    cxr
    wcel
    #
    cmnf
    @1
    clt
    wbr
    #
    @2
    @3
    wb
    cS
    cT
    cF
    cN
    nmofval.1
    nmocl
    #
    @0
    @4
    cc0
    @1
    cle
    wbr
    @5
    @6
    cS
    cT
    cF
    cN
    nmofval.1
    nmoge0
    @1
    ge0gtmnf
    syl2anc
    @4
    @2
    @5
    @3
    @1
    xrrebnd
    baibd
    syl2anc
    bitrd
end
