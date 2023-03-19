include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "scmatf.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "scmatscmid.mm"
include "3expa.mm"
include "wi.mm"
include "scmatrhmval.mm"
include "adantll.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "reximdva.mm"
include "adantr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem scmatfo
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
  assert |- ( ( N e. Fin /\ R e. Ring ) -> F : K -onto-> C )

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
    cK
    cC
    cF
    wf
    vy
    cv
    #
    vc
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vc
    cK
    wrex
    #
    vy
    cC
    wral
    cK
    cC
    cF
    wfo
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
    scmatf
    @2
    @7
    vy
    cC
    @2
    @3
    cC
    wcel
    #
    wa
    @3
    @4
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
    @7
    @0
    @1
    @8
    @11
    cA
    cA
    cbs
    cfv
    #
    cR
    cC
    c.as
    c.1
    cK
    @3
    cN
    crg
    vc
    scmatrhmval.k
    scmatrhmval.a
    @12
    eqid
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.c
    scmatscmid
    3expa
    @2
    @11
    @7
    wi
    @8
    @2
    @10
    @6
    vc
    cK
    @2
    @4
    cK
    wcel
    #
    wa
    #
    @10
    @6
    @14
    @9
    @5
    @3
    @14
    @5
    @9
    @1
    @13
    @5
    @9
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
    @4
    scmatrhmval.k
    scmatrhmval.a
    scmatrhmval.o
    scmatrhmval.t
    scmatrhmval.f
    scmatrhmval
    adantll
    eqcomd
    eqeq2d
    biimpd
    reximdva
    adantr
    mpd
    ralrimiva
    vc
    vy
    cK
    cC
    cF
    dffo3
    sylanbrc
end
