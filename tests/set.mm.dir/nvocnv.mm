include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wcel.mm"
include "simprr.mm"
include "simpll.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "fveq2d.mm"
include "simplr.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqtr2d.mm"
include "jca.mm"
include "impbida.mm"
include "mptcnv.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn5.mm"
include "biimpi.mm"
include "adantr.mm"
include "sylan.mm"
include "cnveqd.mm"
include "3eqtr4d.mm"

theorem nvocnv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  assert |- ( ( F : A --> A /\ A. x e. A ( F ` ( F ` x ) ) = x ) -> `' F = F )

  proof
    cA
    cA
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    cF
    cfv
    #
    @1
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    ccnv
    vy
    cA
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cF
    ccnv
    cF
    @6
    vz
    vy
    cA
    @8
    cA
    @11
    @6
    @7
    cA
    wcel
    #
    @10
    @8
    wceq
    #
    wa
    #
    @10
    cA
    wcel
    #
    @7
    @11
    wceq
    #
    wa
    #
    @6
    @15
    wa
    #
    @16
    @17
    @19
    @10
    @8
    cA
    @6
    @13
    @14
    simprr
    #
    @19
    cA
    cA
    @7
    cF
    @0
    @5
    @15
    simpll
    @6
    @13
    @14
    simprl
    #
    ffvelrnd
    eqeltrd
    @19
    @11
    @8
    cF
    cfv
    #
    @7
    @19
    @10
    @8
    cF
    @20
    fveq2d
    @19
    @13
    @5
    @22
    @7
    wceq
    #
    @21
    @0
    @5
    @15
    simplr
    @4
    @23
    vx
    @7
    cA
    @1
    @7
    wceq
    #
    @3
    @22
    @1
    @7
    @24
    @2
    @8
    cF
    @1
    @7
    cF
    fveq2
    fveq2d
    @24
    id
    eqeq12d
    rspcv
    sylc
    eqtr2d
    jca
    @6
    @18
    wa
    #
    @13
    @14
    @25
    @7
    @11
    cA
    @6
    @16
    @17
    simprr
    #
    @25
    cA
    cA
    @10
    cF
    @0
    @5
    @18
    simpll
    @6
    @16
    @17
    simprl
    #
    ffvelrnd
    eqeltrd
    @25
    @8
    @11
    cF
    cfv
    #
    @10
    @25
    @7
    @11
    cF
    @26
    fveq2d
    @25
    @16
    @5
    @28
    @10
    wceq
    #
    @27
    @0
    @5
    @18
    simplr
    @4
    @29
    vx
    @10
    cA
    @1
    @10
    wceq
    #
    @3
    @28
    @1
    @10
    @30
    @2
    @11
    cF
    @1
    @10
    cF
    fveq2
    fveq2d
    @30
    id
    eqeq12d
    rspcv
    sylc
    eqtr2d
    jca
    impbida
    mptcnv
    @6
    cF
    @9
    @0
    cF
    cA
    wfn
    #
    @5
    cF
    @9
    wceq
    #
    cA
    cA
    cF
    ffn
    #
    @31
    @32
    @5
    @31
    @32
    vz
    cA
    cF
    dffn5
    biimpi
    adantr
    sylan
    cnveqd
    @0
    @31
    @5
    cF
    @12
    wceq
    #
    @33
    @31
    @34
    @5
    @31
    @34
    vy
    cA
    cF
    dffn5
    biimpi
    adantr
    sylan
    3eqtr4d
end
