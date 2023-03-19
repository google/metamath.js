include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "cco1.mm"
include "wceq.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "neeq1.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "mon1pval.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem ismon1p
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  assume uc1pval.p: |- P = ( Poly1 ` R )
  assume uc1pval.b: |- B = ( Base ` P )
  assume uc1pval.z: |- .0. = ( 0g ` P )
  assume uc1pval.d: |- D = ( deg1 ` R )
  assume mon1pval.m: |- M = ( Monic1p ` R )
  assume mon1pval.o: |- .1. = ( 1r ` R )


  assert |- ( F e. M <-> ( F e. B /\ F =/= .0. /\ ( ( coe1 ` F ) ` ( D ` F ) ) = .1. ) )

  proof
    cF
    cM
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
    c.1
    wceq
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
    c.1
    wceq
    #
    wa
    @6
    vf
    cF
    cB
    cM
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
    c.1
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
    eqeq1d
    anbi12d
    cB
    cD
    cP
    cR
    c.1
    vf
    cM
    c.0
    uc1pval.p
    uc1pval.b
    uc1pval.z
    uc1pval.d
    mon1pval.m
    mon1pval.o
    mon1pval
    elrab2
    @0
    @1
    @5
    3anass
    bitr4i
end
