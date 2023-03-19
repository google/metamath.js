include "ctop.mm"
include "wcel.mm"
include "cfil.mm"
include "crn.mm"
include "cuni.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "ccl.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "cfcls.mm"
include "co.mm"
include "anass.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "filunibas.mm"
include "eqcomd.mm"
include "jca.mm"
include "filunirn.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "biimparc.mm"
include "sylanb.mm"
include "impbii.mm"
include "anbi2i.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "ciin.mm"
include "c0.mm"
include "cif.mm"
include "df-fcls.mm"
include "elmpt2cl.mm"
include "fclsval.mm"
include "sylan2b.mm"
include "wi.mm"
include "n0i.mm"
include "iffalse.mm"
include "nsyl2.mm"
include "a1i.mm"
include "pm4.71rd.mm"
include "iftrue.mm"
include "adantl.mm"
include "cvv.mm"
include "elex.mm"
include "wrex.mm"
include "wne.mm"
include "filn0.mm"
include "sylbi.mm"
include "ad2antlr.mm"
include "r19.2z.mm"
include "ex.mm"
include "syl.mm"
include "rexlimivw.mm"
include "syl6.mm"
include "wb.mm"
include "eliin.mm"
include "pm5.21ndd.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "3bitrd.mm"
include "biadan2.mm"
include "3bitr4ri.mm"

theorem isfcls
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vt: setvar t
  let cY: class Y
  assume fclsval.x: |- X = U. J

  disjoint A s
  disjoint F s
  disjoint X s
  disjoint J s
  disjoint f j
  disjoint f x
  disjoint j x
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint j s
  disjoint j t
  disjoint F j
  disjoint s t
  disjoint F t
  disjoint X f
  disjoint X j
  disjoint Y f
  disjoint Y j
  disjoint Y s
  disjoint J f
  disjoint J j
  disjoint J t
  assert |- ( A e. ( J fClus F ) <-> ( J e. Top /\ F e. ( Fil ` X ) /\ A. s e. F A e. ( ( cls ` J ) ` s ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cF
    cfil
    crn
    cuni
    #
    wcel
    #
    wa
    #
    cX
    cF
    cuni
    #
    wceq
    #
    wa
    #
    cA
    vs
    cv
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    vs
    cF
    wral
    #
    wa
    #
    @3
    @5
    @9
    wa
    #
    wa
    @0
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    @9
    w3a
    #
    cA
    cJ
    cF
    cfcls
    co
    #
    wcel
    #
    @3
    @5
    @9
    anass
    @0
    @13
    wa
    #
    @9
    wa
    @0
    @2
    @5
    wa
    #
    wa
    #
    @9
    wa
    @14
    @10
    @17
    @19
    @9
    @13
    @18
    @0
    @13
    @18
    @13
    @2
    @5
    @12
    @1
    cF
    cfil
    cX
    fvssunirn
    sseli
    @13
    @4
    cX
    cF
    cX
    filunibas
    eqcomd
    jca
    @2
    cF
    @4
    cfil
    cfv
    #
    wcel
    #
    @5
    @13
    cF
    filunirn
    #
    @5
    @13
    @21
    @5
    @12
    @20
    cF
    cX
    @4
    cfil
    fveq2
    eleq2d
    biimparc
    sylanb
    impbii
    anbi2i
    anbi1i
    @0
    @13
    @9
    df-3an
    @6
    @19
    @9
    @0
    @2
    @5
    anass
    anbi1i
    3bitr4i
    @16
    @3
    @11
    vj
    vf
    ctop
    @1
    vj
    cv
    #
    cuni
    vf
    cv
    #
    cuni
    wceq
    vx
    @24
    vx
    cv
    @23
    ccl
    cfv
    cfv
    ciin
    c0
    cif
    cJ
    cF
    cfcls
    cA
    vx
    vf
    vj
    df-fcls
    elmpt2cl
    @3
    @16
    cA
    @5
    vs
    cF
    @7
    ciin
    #
    c0
    cif
    #
    wcel
    #
    @5
    @27
    wa
    @11
    @3
    @15
    @26
    cA
    @2
    @0
    @21
    @15
    @26
    wceq
    @22
    vs
    cF
    cJ
    cX
    @4
    fclsval.x
    fclsval
    sylan2b
    eleq2d
    @3
    @27
    @5
    @27
    @5
    wi
    @3
    @27
    @26
    c0
    wceq
    @5
    @26
    cA
    n0i
    @5
    @25
    c0
    iffalse
    nsyl2
    a1i
    pm4.71rd
    @3
    @5
    @27
    @9
    @6
    @27
    cA
    @25
    wcel
    #
    @9
    @6
    @26
    @25
    cA
    @5
    @26
    @25
    wceq
    @3
    @5
    @25
    c0
    iftrue
    adantl
    eleq2d
    @6
    cA
    cvv
    wcel
    #
    @28
    @9
    @28
    @29
    wi
    @6
    cA
    @25
    elex
    a1i
    @6
    @9
    @8
    vs
    cF
    wrex
    #
    @29
    @6
    cF
    c0
    wne
    #
    @9
    @30
    wi
    @2
    @31
    @0
    @5
    @2
    @21
    @31
    @22
    cF
    @4
    filn0
    sylbi
    ad2antlr
    @31
    @9
    @30
    @8
    vs
    cF
    r19.2z
    ex
    syl
    @8
    @29
    vs
    cF
    cA
    @7
    elex
    rexlimivw
    syl6
    @29
    @28
    @9
    wb
    wi
    @6
    vs
    cA
    cF
    @7
    cvv
    eliin
    a1i
    pm5.21ndd
    bitrd
    pm5.32da
    3bitrd
    biadan2
    3bitr4ri
end
