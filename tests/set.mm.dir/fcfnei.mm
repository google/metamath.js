include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cfcf.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "csn.mm"
include "cnei.mm"
include "isfcf.mm"
include "cnt.mm"
include "wss.mm"
include "ctop.mm"
include "cuni.mm"
include "simpll1.mm"
include "topontop.mm"
include "syl.mm"
include "simpr.mm"
include "eqid.mm"
include "neii1.mm"
include "syl2anc.mm"
include "ntrss2.mm"
include "wb.mm"
include "simplr.mm"
include "wceq.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "snssd.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "snssg.mm"
include "mpbird.mm"
include "ntropn.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "ssrin.mm"
include "ssn0.mm"
include "ex.mm"
include "ralimdv.mm"
include "sylsyld.mm"
include "ralrimdva.mm"
include "simpl1.mm"
include "opnneip.mm"
include "3expb.mm"
include "sylan.mm"
include "expr.mm"
include "com23.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem fcfnei
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vo: setvar o
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vy: setvar y
  let cN: class N
  let cS: class S

  disjoint A n
  disjoint n s
  disjoint J n
  disjoint J s
  disjoint L n
  disjoint L s
  disjoint F n
  disjoint F s
  disjoint X n
  disjoint X s
  disjoint Y n
  disjoint Y s
  disjoint n o
  disjoint n x
  disjoint o x
  disjoint A o
  disjoint A x
  disjoint f g
  disjoint f j
  disjoint f n
  disjoint f o
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g j
  disjoint g n
  disjoint g o
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint j n
  disjoint j o
  disjoint j s
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n y
  disjoint o s
  disjoint o y
  disjoint J o
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint L f
  disjoint L g
  disjoint L j
  disjoint L o
  disjoint L x
  disjoint N n
  disjoint N s
  disjoint F f
  disjoint F g
  disjoint F o
  disjoint F x
  disjoint X f
  disjoint X g
  disjoint X j
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y j
  disjoint Y o
  disjoint Y x
  disjoint S s
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fClusf L ) ` F ) <-> ( A e. X /\ A. n e. ( ( nei ` J ) ` { A } ) A. s e. L ( n i^i ( F " s ) ) =/= (/) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cF
    cJ
    cL
    cfcf
    co
    cfv
    wcel
    cA
    cX
    wcel
    #
    cA
    vo
    cv
    #
    wcel
    #
    @5
    cF
    vs
    cv
    cima
    #
    cin
    #
    c0
    wne
    #
    vs
    cL
    wral
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    @4
    vn
    cv
    #
    @7
    cin
    #
    c0
    wne
    #
    vs
    cL
    wral
    #
    vn
    cA
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    wa
    cA
    vo
    cF
    cJ
    cL
    cX
    cY
    vs
    isfcf
    @3
    @4
    @12
    @19
    @3
    @4
    wa
    #
    @12
    @19
    @20
    @12
    @16
    vn
    @18
    @20
    @13
    @18
    wcel
    #
    wa
    #
    @13
    cJ
    cnt
    cfv
    cfv
    #
    @13
    wss
    #
    @12
    @23
    @7
    cin
    #
    c0
    wne
    #
    vs
    cL
    wral
    #
    @16
    @22
    cJ
    ctop
    wcel
    #
    @13
    cJ
    cuni
    #
    wss
    #
    @24
    @22
    @0
    @28
    @0
    @1
    @2
    @4
    @21
    simpll1
    #
    cX
    cJ
    topontop
    #
    syl
    #
    @22
    @28
    @21
    @30
    @33
    @20
    @21
    simpr
    #
    @17
    cJ
    @13
    @29
    @29
    eqid
    #
    neii1
    syl2anc
    #
    @13
    cJ
    @29
    @35
    ntrss2
    syl2anc
    @22
    @12
    cA
    @23
    wcel
    #
    @27
    @22
    @37
    @17
    @23
    wss
    #
    @22
    @21
    @38
    @34
    @22
    @28
    @17
    @29
    wss
    @30
    @21
    @38
    wb
    @33
    @22
    cA
    @29
    @22
    cA
    cX
    @29
    @3
    @4
    @21
    simplr
    #
    @22
    @0
    cX
    @29
    wceq
    @31
    cX
    cJ
    toponuni
    syl
    eleqtrd
    snssd
    @36
    @17
    cJ
    @13
    @29
    @35
    neiint
    syl3anc
    mpbid
    @22
    @4
    @37
    @38
    wb
    @39
    cA
    @23
    cX
    snssg
    syl
    mpbird
    @22
    @23
    cJ
    wcel
    #
    @12
    @37
    @27
    wi
    #
    wi
    @22
    @28
    @30
    @40
    @33
    @36
    @13
    cJ
    @29
    @35
    ntropn
    syl2anc
    @11
    @41
    vo
    @23
    cJ
    @5
    @23
    wceq
    #
    @6
    @37
    @10
    @27
    @5
    @23
    cA
    eleq2
    @42
    @9
    @26
    vs
    cL
    @42
    @8
    @25
    c0
    @5
    @23
    @7
    ineq1
    neeq1d
    ralbidv
    imbi12d
    rspcv
    syl
    mpid
    @24
    @26
    @15
    vs
    cL
    @24
    @25
    @14
    wss
    #
    @26
    @15
    wi
    @23
    @13
    @7
    ssrin
    @43
    @26
    @15
    @25
    @14
    ssn0
    ex
    syl
    ralimdv
    sylsyld
    ralrimdva
    @20
    @19
    @11
    vo
    cJ
    @20
    @5
    cJ
    wcel
    #
    wa
    @6
    @19
    @10
    @20
    @44
    @6
    @19
    @10
    wi
    #
    @20
    @44
    @6
    wa
    #
    wa
    @5
    @18
    wcel
    #
    @45
    @20
    @28
    @46
    @47
    @20
    @0
    @28
    @0
    @1
    @2
    @4
    simpl1
    @32
    syl
    @28
    @44
    @6
    @47
    cA
    cJ
    @5
    opnneip
    3expb
    sylan
    @16
    @10
    vn
    @5
    @18
    @13
    @5
    wceq
    #
    @15
    @9
    vs
    cL
    @48
    @14
    @8
    c0
    @13
    @5
    @7
    ineq1
    neeq1d
    ralbidv
    rspcv
    syl
    expr
    com23
    ralrimdva
    impbid
    pm5.32da
    bitrd
end
