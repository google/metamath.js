include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cfcf.mm"
include "co.mm"
include "cfm.mm"
include "cfcls.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cima.mm"
include "fcfval.mm"
include "eleq2d.mm"
include "wb.mm"
include "simp1.mm"
include "cfbas.mm"
include "toponmax.mm"
include "filfbas.mm"
include "id.mm"
include "fmfil.mm"
include "syl3an.mm"
include "fclsopn.mm"
include "syl2anc.mm"
include "cfg.mm"
include "simpll1.mm"
include "syl.mm"
include "simpll2.mm"
include "simpll3.mm"
include "wceq.mm"
include "simpl2.mm"
include "fgfil.mm"
include "biimpar.mm"
include "eqid.mm"
include "imaelfm.mm"
include "syl31anc.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "rspcv.mm"
include "ralrimdva.mm"
include "wss.mm"
include "wrex.mm"
include "elfm.mm"
include "adantr.mm"
include "simplbda.mm"
include "r19.29r.mm"
include "sslin.mm"
include "ssn0.mm"
include "sylan.mm"
include "rexlimivw.mm"
include "ex.mm"
include "impbid.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem isfcf
  let cA: class A
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vn: setvar n
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vy: setvar y
  let cN: class N
  let cS: class S

  disjoint A o
  disjoint o s
  disjoint J o
  disjoint J s
  disjoint L o
  disjoint L s
  disjoint F o
  disjoint F s
  disjoint X o
  disjoint X s
  disjoint Y o
  disjoint Y s
  disjoint n o
  disjoint n x
  disjoint A n
  disjoint o x
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
  disjoint n s
  disjoint n y
  disjoint J n
  disjoint o y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint L f
  disjoint L g
  disjoint L j
  disjoint L n
  disjoint L x
  disjoint N n
  disjoint N s
  disjoint F f
  disjoint F g
  disjoint F n
  disjoint F x
  disjoint X f
  disjoint X g
  disjoint X j
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y j
  disjoint Y n
  disjoint Y x
  disjoint S s
  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( A e. ( ( J fClusf L ) ` F ) <-> ( A e. X /\ A. o e. J ( A e. o -> A. s e. L ( o i^i ( F " s ) ) =/= (/) ) ) ) )

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
    #
    wcel
    cA
    cJ
    cL
    cX
    cF
    cfm
    co
    cfv
    #
    cfcls
    co
    #
    wcel
    #
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
    @9
    vx
    cv
    #
    cin
    #
    c0
    wne
    #
    vx
    @5
    wral
    #
    wi
    #
    vo
    cJ
    wral
    #
    wa
    #
    @8
    @10
    @9
    cF
    vs
    cv
    #
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
    @3
    @4
    @6
    cA
    cF
    cJ
    cL
    cX
    cY
    fcfval
    eleq2d
    @3
    @0
    @5
    cX
    cfil
    cfv
    wcel
    #
    @7
    @17
    wb
    @0
    @1
    @2
    simp1
    @0
    cX
    cJ
    wcel
    #
    @1
    cL
    cY
    cfbas
    cfv
    wcel
    #
    @2
    @2
    @25
    cX
    cJ
    toponmax
    #
    cL
    cY
    filfbas
    #
    @2
    id
    #
    cJ
    cL
    cF
    cX
    cY
    fmfil
    syl3an
    cA
    vo
    @5
    cJ
    cX
    vx
    fclsopn
    syl2anc
    @3
    @16
    @24
    @8
    @3
    @15
    @23
    vo
    cJ
    @3
    @9
    cJ
    wcel
    #
    wa
    #
    @14
    @22
    @10
    @32
    @14
    @22
    @32
    @14
    @21
    vs
    cL
    @32
    @18
    cL
    wcel
    #
    wa
    #
    @19
    @5
    wcel
    #
    @14
    @21
    wi
    @34
    @26
    @27
    @2
    @18
    cY
    cL
    cfg
    co
    #
    wcel
    #
    @35
    @34
    @0
    @26
    @0
    @1
    @2
    @31
    @33
    simpll1
    @28
    syl
    @34
    @1
    @27
    @0
    @1
    @2
    @31
    @33
    simpll2
    @29
    syl
    @0
    @1
    @2
    @31
    @33
    simpll3
    @32
    @37
    @33
    @32
    @36
    cL
    @18
    @32
    @1
    @36
    cL
    wceq
    @0
    @1
    @2
    @31
    simpl2
    cL
    cY
    fgfil
    syl
    eleq2d
    biimpar
    cJ
    cL
    @18
    cF
    @36
    cX
    cY
    @36
    eqid
    imaelfm
    syl31anc
    @13
    @21
    vx
    @19
    @5
    @11
    @19
    wceq
    @12
    @20
    c0
    @11
    @19
    @9
    ineq2
    neeq1d
    rspcv
    syl
    ralrimdva
    @32
    @22
    @13
    vx
    @5
    @32
    @11
    @5
    wcel
    #
    wa
    @19
    @11
    wss
    #
    vs
    cL
    wrex
    #
    @22
    @13
    wi
    @32
    @38
    @11
    cX
    wss
    #
    @40
    @3
    @38
    @41
    @40
    wa
    wb
    #
    @31
    @0
    @26
    @1
    @27
    @2
    @2
    @42
    @28
    @29
    @30
    vs
    @11
    cL
    cJ
    cF
    cX
    cY
    elfm
    syl3an
    adantr
    simplbda
    @40
    @22
    @13
    @40
    @22
    wa
    @39
    @21
    wa
    #
    vs
    cL
    wrex
    @13
    @39
    @21
    vs
    cL
    r19.29r
    @43
    @13
    vs
    cL
    @39
    @20
    @12
    wss
    @21
    @13
    @19
    @11
    @9
    sslin
    @20
    @12
    ssn0
    sylan
    rexlimivw
    syl
    ex
    syl
    ralrimdva
    impbid
    imbi2d
    ralbidva
    anbi2d
    3bitrd
end
