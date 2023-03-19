include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "scmatrhmval.mm"
include "3adant1.mm"
include "cbs.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "3simpa.mm"
include "simp3.mm"
include "matring.mm"
include "3adant3.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "scmatel.mm"
include "mpbir2and.mm"
include "eqeltrd.mm"

theorem scmatrhmcl
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cX: class X
  let cV: class V
  let vc: setvar c
  assume scmatrhmval.k: |- K = ( Base ` R )
  assume scmatrhmval.a: |- A = ( N Mat R )
  assume scmatrhmval.o: |- .1. = ( 1r ` A )
  assume scmatrhmval.t: |- .* = ( .s ` A )
  assume scmatrhmval.f: |- F = ( x e. K |-> ( x .* .1. ) )
  assume scmatrhmval.c: |- C = ( N ScMat R )

  disjoint K x
  disjoint R x
  disjoint X x
  disjoint .1. x
  disjoint .* x
  disjoint V x
  disjoint K c
  disjoint N c
  disjoint R c
  disjoint X c
  disjoint .* c
  disjoint .1. c
  assert |- ( ( N e. Fin /\ R e. Ring /\ X e. K ) -> ( F ` X ) e. C )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cX
    cK
    wcel
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cX
    c.1
    c.as
    co
    #
    cC
    @1
    @2
    @4
    @5
    wceq
    @0
    vx
    cA
    cR
    c.1
    cF
    c.as
    cK
    cN
    crg
    cX
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    3adant1
    @3
    @5
    cC
    wcel
    #
    @5
    cA
    cbs
    cfv
    #
    wcel
    #
    @5
    vc
    cv
    #
    c.1
    c.as
    co
    #
    wceq
    #
    vc
    cK
    wrex
    #
    @3
    @0
    @1
    wa
    @2
    c.1
    @7
    wcel
    #
    @8
    @0
    @1
    @2
    3simpa
    @0
    @1
    @2
    simp3
    #
    @3
    cA
    crg
    wcel
    #
    @13
    @0
    @1
    @15
    @2
    cA
    cR
    cN
    scmatrhmval.a
    matring
    3adant3
    @7
    cA
    c.1
    @7
    eqid
    #
    scmatrhmval.o
    ringidcl
    syl
    cA
    @7
    cX
    cR
    c.as
    cK
    cN
    c.1
    scmatrhmval.k
    scmatrhmval.a
    @16
    scmatrhmval.t
    matvscl
    syl12anc
    @3
    @11
    @5
    @5
    wceq
    #
    vc
    cX
    cK
    @14
    @9
    cX
    wceq
    #
    @11
    @17
    wb
    @3
    @18
    @10
    @5
    @5
    @9
    cX
    c.1
    c.as
    oveq1
    eqeq2d
    adantl
    @3
    @5
    eqidd
    rspcedvd
    @0
    @1
    @6
    @8
    @12
    wa
    wb
    @2
    cA
    @7
    cR
    cC
    c.as
    c.1
    cK
    @5
    cN
    crg
    vc
    scmatrhmval.k
    scmatrhmval.a
    @16
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.c
    scmatel
    3adant3
    mpbir2and
    eqeltrd
end
