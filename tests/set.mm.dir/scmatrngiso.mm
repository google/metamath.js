include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crg.mm"
include "w3a.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "scmatrhm.mm"
include "3adant2.mm"
include "scmatf1o.mm"
include "wceq.mm"
include "wb.mm"
include "scmatstrbas.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbird.mm"
include "wa.mm"
include "simp3.mm"
include "csubrg.mm"
include "c0g.mm"
include "eqid.mm"
include "scmatsrng.mm"
include "subrgring.mm"
include "isrim.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem scmatrngiso
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
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
  assume scmatghm.s: |- S = ( A |`s C )

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
  disjoint S y
  disjoint S z
  assert |- ( ( N e. Fin /\ N =/= (/) /\ R e. Ring ) -> F e. ( R RingIso S ) )

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
    #
    cF
    cR
    cS
    crs
    co
    wcel
    #
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cK
    cS
    cbs
    cfv
    #
    cF
    wf1o
    #
    @0
    @2
    @5
    @1
    vx
    cA
    cC
    cR
    cS
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
    scmatghm.s
    scmatrhm
    3adant2
    @3
    @7
    cK
    cC
    cF
    wf1o
    #
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
    scmatf1o
    @3
    @6
    cC
    wceq
    #
    @7
    @8
    wb
    @0
    @2
    @9
    @1
    cA
    cC
    cR
    cS
    cN
    scmatrhmval.a
    scmatrhmval.c
    scmatghm.s
    scmatstrbas
    3adant2
    @6
    cC
    cK
    cF
    f1oeq3
    syl
    mpbird
    @3
    @2
    cS
    crg
    wcel
    #
    @4
    @5
    @7
    wa
    wb
    @0
    @1
    @2
    simp3
    @0
    @2
    @10
    @1
    @0
    @2
    wa
    cC
    cA
    csubrg
    cfv
    wcel
    @10
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
    @11
    eqid
    scmatrhmval.k
    @12
    eqid
    scmatrhmval.c
    scmatsrng
    cC
    cA
    cS
    scmatghm.s
    subrgring
    syl
    3adant2
    cK
    @6
    cR
    cS
    cF
    crg
    crg
    scmatrhmval.k
    @6
    eqid
    isrim
    syl2anc
    mpbir2and
end
