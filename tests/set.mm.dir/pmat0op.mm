include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "c0g.mm"
include "cfv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "ply1ring.mm"
include "mat0op.mm"
include "sylan2.mm"

theorem pmat0op
  let cC: class C
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  assume pmatring.p: |- P = ( Poly1 ` R )
  assume pmatring.c: |- C = ( N Mat P )
  assume pmat0op.z: |- .0. = ( 0g ` P )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint P i
  disjoint P j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 0g ` C ) = ( i e. N , j e. N |-> .0. ) )

  proof
    cR
    crg
    wcel
    cN
    cfn
    wcel
    cP
    crg
    wcel
    cC
    c0g
    cfv
    vi
    vj
    cN
    cN
    c.0
    cmpt2
    wceq
    cP
    cR
    pmatring.p
    ply1ring
    cC
    cP
    vi
    vj
    cN
    c.0
    pmatring.c
    pmat0op.z
    mat0op
    sylan2
end
