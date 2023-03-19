include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "cco1.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "neeq1.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "uc1pval.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isuc1p
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let cF: class F
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  assume uc1pval.p: |- P = ( Poly1 ` R )
  assume uc1pval.b: |- B = ( Base ` P )
  assume uc1pval.z: |- .0. = ( 0g ` P )
  assume uc1pval.d: |- D = ( deg1 ` R )
  assume uc1pval.c: |- C = ( Unic1p ` R )
  assume uc1pval.u: |- U = ( Unit ` R )


  assert |- ( F e. C <-> ( F e. B /\ F =/= .0. /\ ( ( coe1 ` F ) ` ( D ` F ) ) e. U ) )

  proof
    cF
    cC
    wcel
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    cF
    cD
    cfv
    #
    cF
    cco1
    cfv
    #
    cfv
    #
    cU
    wcel
    #
    wa
    #
    wa
    @0
    @1
    @5
    w3a
    vf
    cv
    #
    c.0
    wne
    #
    @7
    cD
    cfv
    #
    @7
    cco1
    cfv
    #
    cfv
    #
    cU
    wcel
    #
    wa
    @6
    vf
    cF
    cB
    cC
    @7
    cF
    wceq
    #
    @8
    @1
    @12
    @5
    @7
    cF
    c.0
    neeq1
    @13
    @11
    @4
    cU
    @13
    @9
    @2
    @10
    @3
    @7
    cF
    cco1
    fveq2
    @7
    cF
    cD
    fveq2
    fveq12d
    eleq1d
    anbi12d
    cB
    cC
    cD
    cP
    cR
    cU
    vf
    c.0
    uc1pval.p
    uc1pval.b
    uc1pval.z
    uc1pval.d
    uc1pval.c
    uc1pval.u
    uc1pval
    elrab2
    @0
    @1
    @5
    3anass
    bitr4i
end
