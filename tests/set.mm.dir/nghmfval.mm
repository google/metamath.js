include "cngp.mm"
include "wcel.mm"
include "wa.mm"
include "cnghm.mm"
include "co.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "wceq.mm"
include "cv.mm"
include "cnmo.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "df-nghm.mm"
include "ovexi.mm"
include "cnvex.mm"
include "imaex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "nmoffn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "cnv0.mm"
include "syl6eq.mm"
include "0ima.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem nghmfval
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


  assert |- ( S NGHom T ) = ( `' N " RR )

  proof
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    wa
    #
    cS
    cT
    cnghm
    co
    #
    cN
    ccnv
    #
    cr
    cima
    #
    wceq
    vs
    vt
    cS
    cT
    cngp
    cngp
    vs
    cv
    #
    vt
    cv
    #
    cnmo
    co
    #
    ccnv
    #
    cr
    cima
    #
    @3
    cnghm
    @4
    cS
    wceq
    @5
    cT
    wceq
    wa
    #
    @7
    @2
    cr
    @9
    @6
    cN
    @9
    @6
    cS
    cT
    cnmo
    co
    #
    cN
    @4
    cS
    @5
    cT
    cnmo
    oveq12
    nmofval.1
    syl6eqr
    cnveqd
    imaeq1d
    vt
    vs
    df-nghm
    #
    @2
    cr
    cN
    cN
    cS
    cT
    cnmo
    nmofval.1
    ovexi
    cnvex
    imaex
    ovmpt2a
    @0
    wn
    #
    @1
    c0
    @3
    vs
    vt
    @8
    cnghm
    cS
    cT
    cngp
    cngp
    @11
    mpt2ndm0
    @12
    @3
    c0
    cr
    cima
    c0
    @12
    @2
    c0
    cr
    @12
    @2
    c0
    ccnv
    c0
    @12
    cN
    c0
    @12
    cN
    @10
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
    @13
    wceq
    nmoffn
    @13
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
    eqtr4d
    pm2.61i
end
