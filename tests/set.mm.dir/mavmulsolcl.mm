include "wcel.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "2a1.mm"
include "wn.mm"
include "cdm.mm"
include "cxp.mm"
include "simpl.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "3jca.mm"
include "mavmuldm.mm"
include "syl.mm"
include "intnand.mm"
include "ndmovg.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "f0dom0.mm"
include "biimprd.mm"
include "necon3d.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "a1d.mm"
include "eleq2s.mm"
include "impcom.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "eqcoms.mm"
include "syl6bi.mm"
include "com23.mm"
include "mpcom.mm"
include "ex.mm"
include "pm2.61i.mm"

theorem mavmulsolcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  assume mavmuldm.b: |- B = ( Base ` R )
  assume mavmuldm.c: |- C = ( B ^m ( M X. N ) )
  assume mavmuldm.d: |- D = ( B ^m N )
  assume mavmuldm.t: |- .x. = ( R maVecMul <. M , N >. )
  assume mavmulsolcl.e: |- E = ( B ^m M )


  assert |- ( ( ( M e. Fin /\ N e. Fin /\ M =/= (/) ) /\ ( R e. V /\ Y e. E ) ) -> ( ( A .x. X ) = Y -> X e. D ) )

  proof
    cX
    cD
    wcel
    #
    cM
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    cM
    c0
    wne
    #
    w3a
    #
    cR
    cV
    wcel
    #
    cY
    cE
    wcel
    #
    wa
    #
    wa
    #
    cA
    cX
    c.x
    co
    #
    cY
    wceq
    #
    @0
    wi
    #
    wi
    @0
    @8
    @10
    2a1
    @0
    wn
    #
    @8
    @11
    @9
    c0
    wceq
    #
    @12
    @8
    wa
    #
    @11
    @14
    c.x
    cdm
    cC
    cD
    cxp
    wceq
    #
    cA
    cC
    wcel
    #
    @0
    wa
    wn
    @13
    @14
    @5
    @1
    @2
    w3a
    #
    @15
    @8
    @17
    @12
    @8
    @5
    @1
    @2
    @7
    @5
    @4
    @5
    @6
    simpl
    adantl
    @1
    @2
    @3
    @7
    simpl1
    @1
    @2
    @3
    @7
    simpl2
    3jca
    adantl
    cB
    cC
    cD
    cR
    c.x
    cM
    cN
    cV
    mavmuldm.b
    mavmuldm.c
    mavmuldm.d
    mavmuldm.t
    mavmuldm
    syl
    @14
    @0
    @16
    @12
    @8
    simpl
    intnand
    cA
    cX
    cC
    cD
    c.x
    ndmovg
    syl2anc
    @13
    @10
    @14
    @0
    @13
    @10
    c0
    cY
    wceq
    @14
    @0
    wi
    #
    @9
    c0
    cY
    eqeq1
    @18
    cY
    c0
    @14
    cY
    c0
    wceq
    #
    @0
    @8
    @19
    @0
    wi
    @12
    @8
    cY
    c0
    wne
    #
    @19
    @0
    @7
    @4
    @20
    @6
    @5
    @4
    @20
    wi
    #
    @5
    @21
    wi
    #
    cY
    cB
    cM
    cmap
    co
    #
    cE
    cY
    @23
    wcel
    cM
    cB
    cY
    wf
    #
    @22
    cY
    cB
    cM
    elmapi
    @24
    @21
    @5
    @4
    @24
    @20
    @3
    @1
    @24
    @20
    wi
    @2
    @24
    @3
    @20
    @24
    cY
    c0
    cM
    c0
    @24
    cM
    c0
    wceq
    @19
    cY
    cM
    cB
    f0dom0
    biimprd
    necon3d
    com12
    3ad2ant3
    com12
    a1d
    syl
    mavmulsolcl.e
    eleq2s
    impcom
    impcom
    @0
    cY
    c0
    eqneqall
    syl5com
    adantl
    com12
    eqcoms
    syl6bi
    com23
    mpcom
    ex
    pm2.61i
end
