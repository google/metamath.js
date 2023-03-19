include "cv.mm"
include "csn.mm"
include "cixp.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "sneq.mm"
include "ixpeq1d.mm"
include "eleq2d.mm"
include "opeq1.mm"
include "sneqd.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "cvv.mm"
include "elex.mm"
include "snex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "vex.mm"
include "elixp.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "anbi2i.mm"
include "wf.mm"
include "simpl.mm"
include "biimpri.mm"
include "adantl.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "fsn2.mm"
include "sylib.mm"
include "opeq2.mm"
include "rspcev.mm"
include "syl.mm"
include "fvsn.mm"
include "id.mm"
include "syl5eqel.mm"
include "fnsn.mm"
include "jctil.mm"
include "fneq1.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "impbii.mm"
include "3bitri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem elixpsn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vz: setvar z
  let vw: setvar w

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint V x
  disjoint V y
  disjoint B z
  disjoint B w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint F z
  disjoint F w
  disjoint A z
  disjoint A w
  disjoint V z
  disjoint V w
  assert |- ( A e. V -> ( F e. X_ x e. { A } B <-> E. y e. B F = { <. A , y >. } ) )

  proof
    cF
    vx
    vz
    cv
    #
    csn
    #
    cB
    cixp
    #
    wcel
    #
    cF
    @0
    vy
    cv
    #
    cop
    #
    csn
    #
    wceq
    #
    vy
    cB
    wrex
    #
    cF
    vx
    cA
    csn
    #
    cB
    cixp
    #
    wcel
    cF
    cA
    @4
    cop
    #
    csn
    #
    wceq
    #
    vy
    cB
    wrex
    vz
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @10
    cF
    @14
    vx
    @1
    @9
    cB
    @0
    cA
    sneq
    ixpeq1d
    eleq2d
    @14
    @7
    @13
    vy
    cB
    @14
    @6
    @12
    cF
    @14
    @5
    @11
    @0
    cA
    @4
    opeq1
    sneqd
    eqeq2d
    rexbidv
    @3
    cF
    cvv
    wcel
    #
    @8
    cF
    @2
    elex
    @7
    @15
    vy
    cB
    @7
    @15
    @6
    cvv
    wcel
    @5
    snex
    cF
    @6
    cvv
    eleq1
    mpbiri
    rexlimivw
    vw
    cv
    #
    @2
    wcel
    #
    @16
    @6
    wceq
    #
    vy
    cB
    wrex
    #
    @3
    @8
    vw
    cF
    cvv
    @16
    cF
    @2
    eleq1
    @16
    cF
    wceq
    @18
    @7
    vy
    cB
    @16
    cF
    @6
    eqeq1
    rexbidv
    @17
    @16
    @1
    wfn
    #
    vx
    cv
    #
    @16
    cfv
    #
    cB
    wcel
    #
    vx
    @1
    wral
    #
    wa
    @20
    @0
    @16
    cfv
    #
    cB
    wcel
    #
    wa
    #
    @19
    vx
    @1
    cB
    @16
    vw
    vex
    elixp
    @24
    @26
    @20
    @23
    @26
    vx
    @0
    vz
    vex
    #
    @21
    @0
    wceq
    @22
    @25
    cB
    @21
    @0
    @16
    fveq2
    eleq1d
    ralsn
    anbi2i
    @27
    @19
    @27
    @26
    @16
    @0
    @25
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    @19
    @27
    @1
    cB
    @16
    wf
    #
    @32
    @27
    @20
    @4
    @16
    cfv
    #
    cB
    wcel
    #
    vy
    @1
    wral
    #
    @33
    @20
    @26
    simpl
    @26
    @36
    @20
    @36
    @26
    @35
    @26
    vy
    @0
    @28
    @4
    @0
    wceq
    @34
    @25
    cB
    @4
    @0
    @16
    fveq2
    eleq1d
    ralsn
    biimpri
    adantl
    vy
    @1
    cB
    @16
    ffnfv
    sylanbrc
    @0
    cB
    @16
    @28
    fsn2
    sylib
    @18
    @31
    vy
    @25
    cB
    @4
    @25
    wceq
    #
    @6
    @30
    @16
    @37
    @5
    @29
    @4
    @25
    @0
    opeq2
    sneqd
    eqeq2d
    rspcev
    syl
    @18
    @27
    vy
    cB
    @4
    cB
    wcel
    #
    @27
    @18
    @6
    @1
    wfn
    #
    @0
    @6
    cfv
    #
    cB
    wcel
    #
    wa
    @38
    @41
    @39
    @38
    @40
    @4
    cB
    @0
    @4
    @28
    vy
    vex
    #
    fvsn
    @38
    id
    syl5eqel
    @0
    @4
    @28
    @42
    fnsn
    jctil
    @18
    @20
    @39
    @26
    @41
    @1
    @16
    @6
    fneq1
    @18
    @25
    @40
    cB
    @0
    @16
    @6
    fveq1
    eleq1d
    anbi12d
    syl5ibrcom
    rexlimiv
    impbii
    3bitri
    vtoclbg
    pm5.21nii
    vtoclbg
end
