include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "pmat0op.mm"
include "wceq.mm"
include "ply1scl0.mm"
include "eqcomd.mm"
include "adantl.mm"
include "mpt2eq3dv.mm"
include "eqtrd.mm"

theorem pmat0opsc
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  assume pmat0opsc.p: |- P = ( Poly1 ` R )
  assume pmat0opsc.c: |- C = ( N Mat P )
  assume pmat0opsc.a: |- A = ( algSc ` P )
  assume pmat0opsc.z: |- .0. = ( 0g ` R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 0g ` C ) = ( i e. N , j e. N |-> ( A ` .0. ) ) )

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
    cC
    c0g
    cfv
    vi
    vj
    cN
    cN
    cP
    c0g
    cfv
    #
    cmpt2
    vi
    vj
    cN
    cN
    c.0
    cA
    cfv
    #
    cmpt2
    cC
    cP
    cR
    vi
    vj
    cN
    @3
    pmat0opsc.p
    pmat0opsc.c
    @3
    eqid
    #
    pmat0op
    @2
    vi
    vj
    cN
    cN
    @3
    @4
    @1
    @3
    @4
    wceq
    @0
    @1
    @4
    @3
    cA
    cP
    cR
    @3
    c.0
    pmat0opsc.p
    pmat0opsc.a
    pmat0opsc.z
    @5
    ply1scl0
    eqcomd
    adantl
    mpt2eq3dv
    eqtrd
end
