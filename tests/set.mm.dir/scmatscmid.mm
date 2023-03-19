include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "scmatel.mm"
include "simplbda.mm"
include "3impa.mm"

theorem scmatscmid
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  assume scmatval.k: |- K = ( Base ` R )
  assume scmatval.a: |- A = ( N Mat R )
  assume scmatval.b: |- B = ( Base ` A )
  assume scmatval.1: |- .1. = ( 1r ` A )
  assume scmatval.t: |- .x. = ( .s ` A )
  assume scmatval.s: |- S = ( N ScMat R )

  disjoint K c
  disjoint N c
  disjoint R c
  disjoint M c
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint K n
  disjoint K r
  disjoint c n
  disjoint c r
  disjoint N a
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint a c
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint c m
  disjoint R a
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint V a
  disjoint V n
  disjoint V r
  disjoint .1. n
  disjoint .1. r
  disjoint .x. n
  disjoint .x. r
  disjoint K m
  disjoint M m
  disjoint .1. m
  disjoint .x. m
  assert |- ( ( N e. Fin /\ R e. V /\ M e. S ) -> E. c e. K M = ( c .x. .1. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cS
    wcel
    #
    cM
    vc
    cv
    c.1
    c.x
    co
    wceq
    vc
    cK
    wrex
    #
    @0
    @1
    wa
    @2
    cM
    cB
    wcel
    @3
    cA
    cB
    cR
    cS
    c.x
    c.1
    cK
    cM
    cN
    cV
    vc
    scmatval.k
    scmatval.a
    scmatval.b
    scmatval.1
    scmatval.t
    scmatval.s
    scmatel
    simplbda
    3impa
end
