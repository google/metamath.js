include "clo.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "chil.mm"
include "wral.mm"
include "wa.mm"
include "cho.mm"
include "cid.mm"
include "cres.mm"
include "cif.mm"
include "eleq1.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "idlnop.mm"
include "fvresi.mm"
include "hiidrcl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "lnophmi.mm"
include "dedth.mm"

theorem lnophm
  let vx: setvar x
  let cT: class T
  let vy: setvar y
  let cA: class A
  let cU: class U

  disjoint T x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint T y
  disjoint U x
  disjoint U y
  assert |- ( ( T e. LinOp /\ A. x e. ~H ( x .ih ( T ` x ) ) e. RR ) -> T e. HrmOp )

  proof
    cT
    clo
    wcel
    #
    vx
    cv
    #
    @1
    cT
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    vx
    chil
    wral
    #
    wa
    #
    cT
    cho
    wcel
    @6
    cT
    cid
    chil
    cres
    #
    cif
    #
    cho
    wcel
    cT
    @7
    cT
    @8
    cho
    eleq1
    vy
    @8
    @8
    clo
    wcel
    #
    vy
    cv
    #
    @10
    @8
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    vy
    chil
    wral
    #
    @6
    @9
    @14
    wa
    @7
    clo
    wcel
    #
    @10
    @10
    @7
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    vy
    chil
    wral
    #
    wa
    cT
    @7
    cT
    @8
    wceq
    #
    @0
    @9
    @5
    @14
    cT
    @8
    clo
    eleq1
    @5
    @10
    @10
    cT
    cfv
    #
    csp
    co
    #
    cr
    wcel
    #
    vy
    chil
    wral
    @20
    @14
    @4
    @23
    vx
    vy
    chil
    @1
    @10
    wceq
    #
    @3
    @22
    cr
    @24
    @1
    @10
    @2
    @21
    csp
    @24
    id
    @1
    @10
    cT
    fveq2
    oveq12d
    eleq1d
    cbvralv
    @20
    @23
    @13
    vy
    chil
    @20
    @22
    @12
    cr
    @20
    @21
    @11
    @10
    csp
    @10
    cT
    @8
    fveq1
    oveq2d
    eleq1d
    ralbidv
    syl5bb
    anbi12d
    @7
    @8
    wceq
    #
    @15
    @9
    @19
    @14
    @7
    @8
    clo
    eleq1
    @25
    @18
    @13
    vy
    chil
    @25
    @17
    @12
    cr
    @25
    @16
    @11
    @10
    csp
    @10
    @7
    @8
    fveq1
    oveq2d
    eleq1d
    ralbidv
    anbi12d
    @15
    @19
    idlnop
    @18
    vy
    chil
    @10
    chil
    wcel
    #
    @17
    @10
    @10
    csp
    co
    cr
    @26
    @16
    @10
    @10
    csp
    chil
    @10
    fvresi
    oveq2d
    @10
    hiidrcl
    eqeltrd
    rgen
    pm3.2i
    elimhyp
    #
    simpli
    @9
    @14
    @27
    simpri
    lnophmi
    dedth
end
