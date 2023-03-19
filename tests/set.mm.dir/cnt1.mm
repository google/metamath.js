include "ct1.mm"
include "wcel.mm"
include "wf1.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wral.mm"
include "cntop1.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "ffn.mm"
include "syl.mm"
include "fnsnfv.mm"
include "sylan.mm"
include "imaeq2d.mm"
include "wss.mm"
include "simpl2.mm"
include "cdm.mm"
include "fdm.mm"
include "f1dm.mm"
include "3ad2ant2.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "snssd.mm"
include "f1imacnv.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simpl3.mm"
include "simpl1.mm"
include "ffvelrnda.mm"
include "t1sncld.mm"
include "cnclima.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "ist1.mm"
include "sylanbrc.mm"

theorem cnt1
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V


  assert |- ( ( K e. Fre /\ F : X -1-1-> Y /\ F e. ( J Cn K ) ) -> J e. Fre )

  proof
    cK
    ct1
    wcel
    #
    cX
    cY
    cF
    wf1
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cJ
    ctop
    wcel
    #
    vx
    cv
    #
    csn
    #
    cJ
    ccld
    cfv
    #
    wcel
    #
    vx
    cJ
    cuni
    #
    wral
    cJ
    ct1
    wcel
    @2
    @0
    @4
    @1
    cF
    cJ
    cK
    cntop1
    3ad2ant3
    @3
    @8
    vx
    @9
    @3
    @5
    @9
    wcel
    #
    wa
    #
    cF
    ccnv
    #
    @5
    cF
    cfv
    #
    csn
    #
    cima
    #
    @6
    @7
    @11
    @15
    @12
    cF
    @6
    cima
    #
    cima
    #
    @6
    @11
    @14
    @16
    @12
    @3
    cF
    @9
    wfn
    #
    @10
    @14
    @16
    wceq
    @3
    @9
    cK
    cuni
    #
    cF
    wf
    #
    @18
    @2
    @0
    @20
    @1
    cF
    cJ
    cK
    @9
    @19
    @9
    eqid
    #
    @19
    eqid
    #
    cnf
    3ad2ant3
    #
    @9
    @19
    cF
    ffn
    syl
    @9
    @5
    cF
    fnsnfv
    sylan
    imaeq2d
    @11
    @1
    @6
    cX
    wss
    @17
    @6
    wceq
    @0
    @1
    @2
    @10
    simpl2
    @11
    @5
    cX
    @3
    @10
    @5
    cX
    wcel
    @3
    @9
    cX
    @5
    @3
    cF
    cdm
    #
    @9
    cX
    @3
    @20
    @24
    @9
    wceq
    @23
    @9
    @19
    cF
    fdm
    syl
    @1
    @0
    @24
    cX
    wceq
    @2
    cX
    cY
    cF
    f1dm
    3ad2ant2
    eqtr3d
    eleq2d
    biimpa
    snssd
    cX
    cY
    @6
    cF
    f1imacnv
    syl2anc
    eqtrd
    @11
    @2
    @14
    cK
    ccld
    cfv
    wcel
    #
    @15
    @7
    wcel
    @0
    @1
    @2
    @10
    simpl3
    @11
    @0
    @13
    @19
    wcel
    @25
    @0
    @1
    @2
    @10
    simpl1
    @3
    @9
    @19
    @5
    cF
    @23
    ffvelrnda
    @13
    cK
    @19
    @22
    t1sncld
    syl2anc
    @14
    cF
    cJ
    cK
    cnclima
    syl2anc
    eqeltrrd
    ralrimiva
    cJ
    @9
    vx
    @21
    ist1
    sylanbrc
end
