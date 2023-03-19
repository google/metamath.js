include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "mat0.mm"
include "csn.mm"
include "fconstmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "simpr.mm"
include "sqxpexg.mm"
include "adantr.mm"
include "frlm0.mm"
include "syl2anc.mm"
include "cv.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"

theorem mat0op
  let cA: class A
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  assume mat0op.a: |- A = ( N Mat R )
  assume mat0op.z: |- .0. = ( 0g ` R )

  disjoint i j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 0g ` A ) = ( i e. N , j e. N |-> .0. ) )

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
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    c0g
    cfv
    #
    cA
    c0g
    cfv
    vi
    vj
    cN
    cN
    c.0
    cmpt2
    #
    cA
    cR
    @4
    cN
    crg
    mat0op.a
    @4
    eqid
    #
    mat0
    @2
    @3
    cR
    c0g
    cfv
    #
    csn
    cxp
    #
    vi
    vj
    cN
    cN
    @8
    cmpt2
    #
    @5
    @6
    vi
    vj
    cN
    cN
    @8
    fconstmpt2
    @2
    @1
    @3
    cvv
    wcel
    #
    @9
    @5
    wceq
    @0
    @1
    simpr
    @0
    @11
    @1
    cN
    cfn
    sqxpexg
    adantr
    cR
    @4
    @3
    cvv
    @8
    @7
    @8
    eqid
    frlm0
    syl2anc
    @10
    @6
    wceq
    @2
    vi
    vj
    cN
    cN
    @8
    c.0
    @8
    c.0
    wceq
    vi
    cv
    cN
    wcel
    vj
    cv
    cN
    wcel
    wa
    c.0
    @8
    mat0op.z
    eqcomi
    a1i
    mpt2eq3ia
    a1i
    3eqtr3a
    eqtr3d
end
