include "cre.mm"
include "cv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cim.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "cmbf.mm"
include "wceq.mm"
include "coeq2.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "df-mbf.mm"
include "elrab2.mm"

theorem ismbf1
  let vx: setvar x
  let cF: class F
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint F x
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  assert |- ( F e. MblFn <-> ( F e. ( CC ^pm RR ) /\ A. x e. ran (,) ( ( `' ( Re o. F ) " x ) e. dom vol /\ ( `' ( Im o. F ) " x ) e. dom vol ) ) )

  proof
    cre
    vf
    cv
    #
    ccom
    #
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    cim
    @0
    ccom
    #
    ccnv
    #
    @3
    cima
    #
    @5
    wcel
    #
    wa
    #
    vx
    cioo
    crn
    #
    wral
    cre
    cF
    ccom
    #
    ccnv
    #
    @3
    cima
    #
    @5
    wcel
    #
    cim
    cF
    ccom
    #
    ccnv
    #
    @3
    cima
    #
    @5
    wcel
    #
    wa
    #
    vx
    @12
    wral
    vf
    cF
    cc
    cr
    cpm
    co
    cmbf
    @0
    cF
    wceq
    #
    @11
    @21
    vx
    @12
    @22
    @6
    @16
    @10
    @20
    @22
    @4
    @15
    @5
    @22
    @2
    @14
    @3
    @22
    @1
    @13
    @0
    cF
    cre
    coeq2
    cnveqd
    imaeq1d
    eleq1d
    @22
    @9
    @19
    @5
    @22
    @8
    @18
    @3
    @22
    @7
    @17
    @0
    cF
    cim
    coeq2
    cnveqd
    imaeq1d
    eleq1d
    anbi12d
    ralbidv
    vx
    vf
    df-mbf
    elrab2
end
