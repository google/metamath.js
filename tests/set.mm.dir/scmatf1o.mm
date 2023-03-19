include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crg.mm"
include "w3a.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "scmatf1.mm"
include "scmatfo.mm"
include "3adant2.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem scmatf1o
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
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
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
  disjoint C c
  disjoint C y
  disjoint c y
  disjoint F c
  disjoint F y
  disjoint K y
  disjoint N y
  disjoint c x
  disjoint x y
  disjoint R y
  disjoint F z
  disjoint K i
  disjoint K j
  disjoint K z
  disjoint i j
  disjoint i z
  disjoint j z
  disjoint N i
  disjoint N j
  disjoint N z
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x z
  disjoint y z
  disjoint R i
  disjoint R j
  disjoint R z
  disjoint .1. i
  disjoint .1. j
  disjoint .* i
  disjoint .* j
  assert |- ( ( N e. Fin /\ N =/= (/) /\ R e. Ring ) -> F : K -1-1-onto-> C )

  proof
    cN
    cfn
    wcel
    #
    cN
    c0
    wne
    #
    cR
    crg
    wcel
    #
    w3a
    cK
    cC
    cF
    wf1
    cK
    cC
    cF
    wfo
    #
    cK
    cC
    cF
    wf1o
    vx
    cA
    cC
    cR
    c.1
    cF
    c.as
    cK
    cN
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval.c
    scmatf1
    @0
    @2
    @3
    @1
    vx
    cA
    cC
    cR
    c.1
    cF
    c.as
    cK
    cN
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval.c
    scmatfo
    3adant2
    cK
    cC
    cF
    df-f1o
    sylanbrc
end
