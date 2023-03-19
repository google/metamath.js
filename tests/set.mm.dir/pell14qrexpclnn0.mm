include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cdiv.mm"
include "pell14qrre.mm"
include "recnd.mm"
include "exp0d.mm"
include "pell14qrne0.mm"
include "dividd.mm"
include "eqtr4d.mm"
include "pell14qrdivcl.mm"
include "3anidm23.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cmul.mm"
include "cc.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "expp1d.mm"
include "simp2l.mm"
include "simp3.mm"
include "simp2r.mm"
include "pell14qrmulcl.mm"
include "syl3anc.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expdcom.mm"
include "3imp.mm"

theorem pell14qrexpclnn0
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e. NN0 ) -> ( A ^ B ) e. ( Pell14QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cB
    cn0
    wcel
    #
    cA
    cB
    cexp
    co
    #
    @1
    wcel
    #
    @3
    @0
    @2
    @5
    @0
    @2
    wa
    #
    cA
    va
    cv
    #
    cexp
    co
    #
    @1
    wcel
    #
    wi
    @6
    cA
    cc0
    cexp
    co
    #
    @1
    wcel
    #
    wi
    @6
    cA
    vb
    cv
    #
    cexp
    co
    #
    @1
    wcel
    #
    wi
    @6
    cA
    @12
    c1
    caddc
    co
    #
    cexp
    co
    #
    @1
    wcel
    #
    wi
    @6
    @5
    wi
    va
    vb
    cB
    @7
    cc0
    wceq
    #
    @9
    @11
    @6
    @18
    @8
    @10
    @1
    @7
    cc0
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    va
    vb
    weq
    #
    @9
    @14
    @6
    @19
    @8
    @13
    @1
    @7
    @12
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @7
    @15
    wceq
    #
    @9
    @17
    @6
    @20
    @8
    @16
    @1
    @7
    @15
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @7
    cB
    wceq
    #
    @9
    @5
    @6
    @21
    @8
    @4
    @1
    @7
    cB
    cA
    cexp
    oveq2
    eleq1d
    imbi2d
    @6
    @10
    cA
    cA
    cdiv
    co
    #
    @1
    @6
    @10
    c1
    @22
    @6
    cA
    @6
    cA
    cA
    cD
    pell14qrre
    recnd
    #
    exp0d
    @6
    cA
    @23
    cA
    cD
    pell14qrne0
    dividd
    eqtr4d
    @0
    @2
    @22
    @1
    wcel
    cA
    cA
    cD
    pell14qrdivcl
    3anidm23
    eqeltrd
    @12
    cn0
    wcel
    #
    @6
    @14
    @17
    @24
    @6
    @14
    @17
    @24
    @6
    @14
    w3a
    #
    @16
    @13
    cA
    cmul
    co
    #
    @1
    @25
    cA
    @12
    @6
    @24
    cA
    cc
    wcel
    @14
    @23
    3ad2ant2
    @24
    @6
    @14
    simp1
    expp1d
    @25
    @0
    @14
    @2
    @26
    @1
    wcel
    @24
    @0
    @2
    @14
    simp2l
    @24
    @6
    @14
    simp3
    @24
    @0
    @2
    @14
    simp2r
    @13
    cA
    cD
    pell14qrmulcl
    syl3anc
    eqeltrd
    3exp
    a2d
    nn0ind
    expdcom
    3imp
end
