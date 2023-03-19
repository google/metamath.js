include "ctop.mm"
include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wa.mm"
include "cfcls.mm"
include "co.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "ccl.mm"
include "ciin.mm"
include "c0.mm"
include "cif.mm"
include "crn.mm"
include "cvv.mm"
include "simpl.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "adantl.mm"
include "wne.mm"
include "wral.mm"
include "filn0.mm"
include "fvex.mm"
include "rgenw.mm"
include "iinexg.mm"
include "sylancl.mm"
include "0ex.mm"
include "ifcl.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeqan12d.mm"
include "iineq1.mm"
include "simpll.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "iineq2dv.mm"
include "eqtrd.mm"
include "ifbieq1d.mm"
include "df-fcls.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "wb.mm"
include "filunibas.mm"
include "eqeq2d.mm"
include "ifbid.mm"

theorem fclsval
  let vt: setvar t
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let cA: class A
  let vs: setvar s
  assume fclsval.x: |- X = U. J

  disjoint F t
  disjoint J t
  disjoint f j
  disjoint f x
  disjoint j x
  disjoint A s
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint j s
  disjoint j t
  disjoint F j
  disjoint s t
  disjoint F s
  disjoint X f
  disjoint X j
  disjoint X s
  disjoint Y f
  disjoint Y j
  disjoint Y s
  disjoint J f
  disjoint J j
  disjoint J s
  assert |- ( ( J e. Top /\ F e. ( Fil ` Y ) ) -> ( J fClus F ) = if ( X = Y , |^|_ t e. F ( ( cls ` J ) ` t ) , (/) ) )

  proof
    cJ
    ctop
    wcel
    #
    cF
    cY
    cfil
    cfv
    #
    wcel
    #
    wa
    #
    cJ
    cF
    cfcls
    co
    #
    cX
    cF
    cuni
    #
    wceq
    #
    vt
    cF
    vt
    cv
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    ciin
    #
    c0
    cif
    #
    cX
    cY
    wceq
    #
    @10
    c0
    cif
    @3
    @0
    cF
    cfil
    crn
    cuni
    #
    wcel
    #
    @11
    cvv
    wcel
    #
    @4
    @11
    wceq
    @0
    @2
    simpl
    @2
    @14
    @0
    @1
    @13
    cF
    cfil
    cY
    fvssunirn
    sseli
    adantl
    @3
    @10
    cvv
    wcel
    #
    c0
    cvv
    wcel
    @15
    @3
    cF
    c0
    wne
    #
    @9
    cvv
    wcel
    #
    vt
    cF
    wral
    @16
    @2
    @17
    @0
    cF
    cY
    filn0
    adantl
    @18
    vt
    cF
    @7
    @8
    fvex
    rgenw
    vt
    cF
    @9
    cvv
    iinexg
    sylancl
    0ex
    @6
    @10
    c0
    cvv
    ifcl
    sylancl
    vj
    vf
    cJ
    cF
    ctop
    @13
    vj
    cv
    #
    cuni
    #
    vf
    cv
    #
    cuni
    #
    wceq
    #
    vt
    @21
    @7
    @19
    ccl
    cfv
    #
    cfv
    #
    ciin
    #
    c0
    cif
    @11
    cfcls
    cvv
    @19
    cJ
    wceq
    #
    @21
    cF
    wceq
    #
    wa
    #
    @23
    @6
    @26
    @10
    c0
    @27
    @28
    @20
    cX
    @22
    @5
    @27
    @20
    cJ
    cuni
    cX
    @19
    cJ
    unieq
    fclsval.x
    syl6eqr
    @21
    cF
    unieq
    eqeqan12d
    @29
    @26
    vt
    cF
    @25
    ciin
    #
    @10
    @28
    @26
    @30
    wceq
    @27
    vt
    @21
    cF
    @25
    iineq1
    adantl
    @29
    vt
    cF
    @25
    @9
    @29
    @7
    cF
    wcel
    #
    wa
    #
    @7
    @24
    @8
    @32
    @19
    cJ
    ccl
    @27
    @28
    @31
    simpll
    fveq2d
    fveq1d
    iineq2dv
    eqtrd
    ifbieq1d
    vt
    vf
    vj
    df-fcls
    ovmpt2ga
    syl3anc
    @3
    @6
    @12
    @10
    c0
    @2
    @6
    @12
    wb
    @0
    @2
    @5
    cY
    cX
    cF
    cY
    filunibas
    eqeq2d
    adantl
    ifbid
    eqtrd
end
