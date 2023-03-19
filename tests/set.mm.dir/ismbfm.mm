include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "cmap.mm"
include "crab.mm"
include "wa.mm"
include "csiga.mm"
include "crn.mm"
include "wceq.mm"
include "unieq.mm"
include "oveq2d.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "oveq1d.mm"
include "raleq.mm"
include "df-mbfm.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem ismbfm
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cF: class F
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  assume ismbfm.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume ismbfm.2: |- ( ph -> T e. U. ran sigAlgebra )

  disjoint F x
  disjoint S x
  disjoint T x
  disjoint f x
  disjoint F f
  disjoint f s
  disjoint f t
  disjoint S f
  disjoint s t
  disjoint s x
  disjoint S s
  disjoint t x
  disjoint S t
  disjoint T f
  disjoint T s
  disjoint T t
  assert |- ( ph -> ( F e. ( S MblFnM T ) <-> ( F e. ( U. T ^m U. S ) /\ A. x e. T ( `' F " x ) e. S ) ) )

  proof
    wph
    cF
    cS
    cT
    cmbfm
    co
    #
    wcel
    cF
    vf
    cv
    #
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cS
    wcel
    #
    vx
    cT
    wral
    #
    vf
    cT
    cuni
    #
    cS
    cuni
    #
    cmap
    co
    #
    crab
    #
    wcel
    cF
    @9
    wcel
    cF
    ccnv
    #
    @3
    cima
    #
    cS
    wcel
    #
    vx
    cT
    wral
    #
    wa
    wph
    @0
    @10
    cF
    wph
    cS
    csiga
    crn
    cuni
    #
    wcel
    cT
    @15
    wcel
    @0
    @10
    wceq
    ismbfm.1
    ismbfm.2
    vs
    vt
    cS
    cT
    @15
    @15
    @4
    vs
    cv
    #
    wcel
    #
    vx
    vt
    cv
    #
    wral
    #
    vf
    @18
    cuni
    #
    @16
    cuni
    #
    cmap
    co
    #
    crab
    @10
    cmbfm
    @5
    vx
    @18
    wral
    #
    vf
    @20
    @8
    cmap
    co
    #
    crab
    @16
    cS
    wceq
    #
    @19
    @23
    vf
    @22
    @24
    @25
    @21
    @8
    @20
    cmap
    @16
    cS
    unieq
    oveq2d
    @25
    @17
    @5
    vx
    @18
    @16
    cS
    @4
    eleq2
    ralbidv
    rabeqbidv
    @18
    cT
    wceq
    #
    @23
    @6
    vf
    @24
    @9
    @26
    @20
    @7
    @8
    cmap
    @18
    cT
    unieq
    oveq1d
    @5
    vx
    @18
    cT
    raleq
    rabeqbidv
    vx
    vt
    vf
    vs
    df-mbfm
    @6
    vf
    @9
    @7
    @8
    cmap
    ovex
    rabex
    ovmpt2
    syl2anc
    eleq2d
    @6
    @14
    vf
    cF
    @9
    @1
    cF
    wceq
    #
    @5
    @13
    vx
    cT
    @27
    @4
    @12
    cS
    @27
    @2
    @11
    @3
    @1
    cF
    cnveq
    imaeq1d
    eleq1d
    ralbidv
    elrab
    syl6bb
end
