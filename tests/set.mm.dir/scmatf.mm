include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "simpr.mm"
include "cur.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "scmatid.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "jca.mm"
include "smatvscl.mm"
include "syldan.mm"
include "fmptd.mm"

theorem scmatf
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vc: setvar c
  assume scmatrhmval.k: |- K = ( Base ` R )
  assume scmatrhmval.a: |- A = ( N Mat R )
  assume scmatrhmval.o: |- .1. = ( 1r ` A )
  assume scmatrhmval.t: |- .* = ( .s ` A )
  assume scmatrhmval.f: |- F = ( x e. K |-> ( x .* .1. ) )
  assume scmatrhmval.c: |- C = ( N ScMat R )

  disjoint K x
  disjoint R x
  disjoint .1. x
  disjoint .* x
  disjoint C x
  disjoint N x
  disjoint V x
  disjoint X x
  disjoint K c
  disjoint N c
  disjoint R c
  disjoint X c
  disjoint .* c
  disjoint .1. c
  assert |- ( ( N e. Fin /\ R e. Ring ) -> F : K --> C )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    vx
    cK
    vx
    cv
    #
    c.1
    c.as
    co
    #
    cC
    cF
    @0
    @1
    cK
    wcel
    #
    @3
    c.1
    cC
    wcel
    #
    wa
    @2
    cC
    wcel
    @0
    @3
    wa
    @3
    @4
    @0
    @3
    simpr
    @0
    @4
    @3
    @0
    c.1
    cA
    cur
    cfv
    cC
    scmatrhmval.o
    cA
    cA
    cbs
    cfv
    #
    cR
    cC
    cK
    cN
    cR
    c0g
    cfv
    #
    scmatrhmval.a
    @5
    eqid
    scmatrhmval.k
    @6
    eqid
    scmatrhmval.c
    scmatid
    syl5eqel
    adantr
    jca
    cA
    @1
    cR
    cC
    c.as
    cK
    cN
    c.1
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.c
    scmatrhmval.t
    smatvscl
    syldan
    scmatrhmval.f
    fmptd
end
