include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cngp.mm"
include "wa.mm"
include "cghm.mm"
include "cfv.mm"
include "nghmfval.mm"
include "eleq2i.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "cnmo.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "nmoffn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "cnveqd.mm"
include "cnv0.mm"
include "syl6eq.mm"
include "imaeq1d.mm"
include "0ima.mm"
include "nsyl2.mm"
include "cxr.mm"
include "wf.mm"
include "wb.mm"
include "nmof.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "biadan2.mm"
include "bitri.mm"

theorem isnghm
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


  assert |- ( F e. ( S NGHom T ) <-> ( ( S e. NrmGrp /\ T e. NrmGrp ) /\ ( F e. ( S GrpHom T ) /\ ( N ` F ) e. RR ) ) )

  proof
    cF
    cS
    cT
    cnghm
    co
    #
    wcel
    cF
    cN
    ccnv
    #
    cr
    cima
    #
    wcel
    #
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
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
    cr
    wcel
    wa
    #
    wa
    @0
    @2
    cF
    cS
    cT
    cN
    nmofval.1
    nghmfval
    eleq2i
    @3
    @4
    @6
    @3
    @2
    c0
    wceq
    @4
    @2
    cF
    n0i
    @4
    wn
    #
    @2
    c0
    cr
    cima
    c0
    @7
    @1
    c0
    cr
    @7
    @1
    c0
    ccnv
    c0
    @7
    cN
    c0
    @7
    cN
    cS
    cT
    cnmo
    co
    c0
    nmofval.1
    cS
    cT
    cngp
    cnmo
    cnmo
    cngp
    cngp
    cxp
    #
    wfn
    cnmo
    cdm
    @8
    wceq
    nmoffn
    @8
    cnmo
    fndm
    ax-mp
    ndmov
    syl5eq
    cnveqd
    cnv0
    syl6eq
    imaeq1d
    cr
    0ima
    syl6eq
    nsyl2
    @4
    @5
    cxr
    cN
    wf
    cN
    @5
    wfn
    @3
    @6
    wb
    cS
    cT
    cN
    nmofval.1
    nmof
    @5
    cxr
    cN
    ffn
    @5
    cF
    cr
    cN
    elpreima
    3syl
    biadan2
    bitri
end
