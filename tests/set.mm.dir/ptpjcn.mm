include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cuni.mm"
include "cixp.mm"
include "ccn.mm"
include "co.mm"
include "wceq.mm"
include "ptuni.mm"
include "3adant3.mm"
include "syl6reqr.mm"
include "mpteq1d.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "cpt.mm"
include "pttop.mm"
include "syl5eqel.mm"
include "ffvelrn.mm"
include "3adant1.mm"
include "jca.mm"
include "wfn.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "fveq2.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "rspcva.mm"
include "sylan2.mm"
include "3ad2antl3.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq2d.mm"
include "mpbird.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "wex.mm"
include "cab.mm"
include "wss.mm"
include "ctg.mm"
include "ctb.mm"
include "ptbas.mm"
include "bastg.mm"
include "syl.mm"
include "ffn.mm"
include "ptval.mm"
include "syl5eq.mm"
include "sseqtr4d.mm"
include "adantr.mm"
include "ptpjpre2.mm"
include "sseldd.mm"
include "expr.mm"
include "ralrimiv.mm"
include "3impa.mm"
include "iscn2.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"

theorem ptpjcn
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let cY: class Y
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  assume ptpjcn.1: |- Y = U. J
  assume ptpjcn.2: |- J = ( Xt_ ` F )

  disjoint A x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint Y x
  disjoint g k
  disjoint g n
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n s
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint J g
  disjoint J k
  disjoint J n
  disjoint J s
  disjoint J u
  disjoint J w
  disjoint I g
  disjoint I k
  disjoint I n
  disjoint I s
  disjoint I u
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint V g
  disjoint V k
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint Y u
  disjoint U g
  disjoint U k
  disjoint U n
  disjoint U s
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ( A e. V /\ F : A --> Top /\ I e. A ) -> ( x e. Y |-> ( x ` I ) ) e. ( J Cn ( F ` I ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    cI
    cA
    wcel
    #
    w3a
    #
    vx
    cY
    cI
    vx
    cv
    #
    cfv
    #
    cmpt
    vx
    vk
    cA
    vk
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    @5
    cmpt
    #
    cJ
    cI
    cF
    cfv
    #
    ccn
    co
    #
    @3
    vx
    cY
    @9
    @5
    @3
    @9
    cJ
    cuni
    #
    cY
    @0
    @1
    @9
    @13
    wceq
    @2
    vk
    cA
    cF
    cJ
    cV
    ptpjcn.2
    ptuni
    3adant3
    ptpjcn.1
    syl6reqr
    #
    mpteq1d
    @3
    cJ
    ctop
    wcel
    #
    @11
    ctop
    wcel
    #
    wa
    cY
    @11
    cuni
    #
    @10
    wf
    #
    @10
    ccnv
    vu
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vu
    @11
    wral
    #
    wa
    @10
    @12
    wcel
    @3
    @15
    @16
    @3
    cJ
    cF
    cpt
    cfv
    #
    ctop
    ptpjcn.2
    @0
    @1
    @23
    ctop
    wcel
    @2
    cA
    cF
    cV
    pttop
    3adant3
    syl5eqel
    @1
    @2
    @16
    @0
    cA
    ctop
    cI
    cF
    ffvelrn
    3adant1
    jca
    @3
    @18
    @22
    @3
    @18
    @9
    @17
    @10
    wf
    @3
    vx
    @9
    @5
    @17
    @10
    @2
    @0
    @4
    @9
    wcel
    #
    @5
    @17
    wcel
    #
    @1
    @24
    @2
    @6
    @4
    cfv
    #
    @8
    wcel
    #
    vk
    cA
    wral
    #
    @25
    @24
    @4
    cA
    wfn
    @28
    vk
    cA
    @8
    @4
    vx
    vex
    elixp
    simprbi
    @27
    @25
    vk
    cI
    cA
    @6
    cI
    wceq
    #
    @26
    @5
    @8
    @17
    @6
    cI
    @4
    fveq2
    @29
    @7
    @11
    @6
    cI
    cF
    fveq2
    unieqd
    eleq12d
    rspcva
    sylan2
    3ad2antl3
    @10
    eqid
    fmptd
    @3
    cY
    @9
    @17
    @10
    @14
    feq2d
    mpbird
    @0
    @1
    @2
    @22
    @0
    @1
    wa
    #
    @2
    wa
    @21
    vu
    @11
    @30
    @2
    @19
    @11
    wcel
    #
    @21
    @30
    @2
    @31
    wa
    #
    wa
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @33
    cfv
    #
    @34
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @35
    @36
    cuni
    wceq
    vy
    cA
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vw
    cv
    vy
    cA
    @35
    cixp
    wceq
    wa
    vg
    wex
    vw
    cab
    #
    cJ
    @20
    @30
    @37
    cJ
    wss
    @32
    @30
    @37
    @37
    ctg
    cfv
    #
    cJ
    @30
    @37
    ctb
    wcel
    @37
    @38
    wss
    vw
    vy
    vz
    cA
    @37
    vg
    cF
    cV
    @37
    eqid
    #
    ptbas
    @37
    ctb
    bastg
    syl
    @1
    @0
    cF
    cA
    wfn
    #
    cJ
    @38
    wceq
    cA
    ctop
    cF
    ffn
    @0
    @40
    wa
    cJ
    @23
    @38
    ptpjcn.2
    vw
    vy
    vz
    cA
    @37
    vg
    cF
    cV
    @39
    ptval
    syl5eq
    sylan2
    sseqtr4d
    adantr
    vw
    vy
    vz
    vx
    cA
    @37
    @19
    vg
    vk
    cF
    cI
    cV
    @9
    @39
    @9
    eqid
    ptpjpre2
    sseldd
    expr
    ralrimiv
    3impa
    jca
    vu
    @10
    cJ
    @11
    cY
    @17
    ptpjcn.1
    @17
    eqid
    iscn2
    sylanbrc
    eqeltrd
end
