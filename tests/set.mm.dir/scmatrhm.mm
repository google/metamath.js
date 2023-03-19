include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "simpr.mm"
include "csubrg.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "scmatsrng.mm"
include "subrgring.mm"
include "syl.mm"
include "jca.mm"
include "scmatghm.mm"
include "scmatmhm.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem scmatrhm
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
  assert |- ( ( N e. Fin /\ R e. Ring ) -> F e. ( R RingHom S ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    @1
    cS
    crg
    wcel
    #
    wa
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cF
    cR
    cS
    crh
    co
    wcel
    @2
    @1
    @3
    @0
    @1
    simpr
    @2
    cC
    cA
    csubrg
    cfv
    wcel
    @3
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
    @8
    eqid
    scmatrhmval.k
    @9
    eqid
    scmatrhmval.c
    scmatsrng
    cC
    cA
    cS
    scmatghm.s
    subrgring
    syl
    jca
    @2
    @4
    @7
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
    scmatghm
    vx
    cA
    cC
    cR
    cS
    @6
    c.1
    cF
    c.as
    cK
    @5
    cN
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval.c
    scmatghm.s
    @5
    eqid
    #
    @6
    eqid
    #
    scmatmhm
    jca
    cR
    cS
    cF
    @5
    @6
    @10
    @11
    isrhm
    sylanbrc
end
