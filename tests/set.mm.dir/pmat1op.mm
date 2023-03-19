include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "cur.mm"
include "cfv.mm"
include "weq.mm"
include "cif.mm"
include "cmpt2.mm"
include "wceq.mm"
include "ply1ring.mm"
include "mat1.mm"
include "sylan2.mm"

theorem pmat1op
  let cC: class C
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  assume pmatring.p: |- P = ( Poly1 ` R )
  assume pmatring.c: |- C = ( N Mat P )
  assume pmat0op.z: |- .0. = ( 0g ` P )
  assume pmat1op.o: |- .1. = ( 1r ` P )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint C i
  disjoint C j
  disjoint .0. i
  disjoint .0. j
  disjoint .1. i
  disjoint .1. j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` C ) = ( i e. N , j e. N |-> if ( i = j , .1. , .0. ) ) )

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
    cur
    cfv
    vi
    vj
    cN
    cN
    vi
    vj
    weq
    c.1
    c.0
    cif
    cmpt2
    wceq
    cP
    cR
    pmatring.p
    ply1ring
    cC
    cP
    c.1
    vi
    vj
    cN
    c.0
    pmatring.c
    pmat1op.o
    pmat0op.z
    mat1
    sylan2
end
