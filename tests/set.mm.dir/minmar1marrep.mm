include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cminmar1.mm"
include "co.mm"
include "cfv.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cmarrep.mm"
include "wceq.mm"
include "eqid.mm"
include "minmar1val0.mm"
include "adantl.mm"
include "cbs.mm"
include "simpr.mm"
include "ringidcl.mm"
include "adantr.mm"
include "marrepval0.mm"
include "syl2anc.mm"
include "eqtr4d.mm"

theorem minmar1marrep
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume minmar1marrep.a: |- A = ( N Mat R )
  assume minmar1marrep.b: |- B = ( Base ` A )
  assume minmar1marrep.q: |- Q = ( N matRRep R )
  assume minmar1marrep.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ M e. B ) -> ( ( N minMatR1 R ) ` M ) = ( M ( N matRRep R ) .1. ) )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    cM
    cN
    cR
    cminmar1
    co
    #
    cfv
    #
    vk
    vl
    cN
    cN
    vi
    vj
    cN
    cN
    vi
    vk
    weq
    vj
    vl
    weq
    c.1
    cR
    c0g
    cfv
    #
    cif
    vi
    cv
    vj
    cv
    cM
    co
    cif
    cmpt2
    cmpt2
    #
    cM
    c.1
    cN
    cR
    cmarrep
    co
    #
    co
    #
    @1
    @4
    @6
    wceq
    @0
    cA
    cB
    @3
    cR
    c.1
    vi
    vj
    vk
    cM
    cN
    @5
    vl
    minmar1marrep.a
    minmar1marrep.b
    @3
    eqid
    minmar1marrep.o
    @5
    eqid
    #
    minmar1val0
    adantl
    @2
    @1
    c.1
    cR
    cbs
    cfv
    #
    wcel
    #
    @8
    @6
    wceq
    @0
    @1
    simpr
    @0
    @11
    @1
    @10
    cR
    c.1
    @10
    eqid
    minmar1marrep.o
    ringidcl
    adantr
    cA
    cB
    @7
    cR
    c.1
    vi
    vj
    vk
    cM
    cN
    @5
    vl
    minmar1marrep.a
    minmar1marrep.b
    @7
    eqid
    @9
    marrepval0
    syl2anc
    eqtr4d
end
