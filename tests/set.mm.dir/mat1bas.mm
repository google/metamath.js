include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cmat.mm"
include "co.mm"
include "eqid.mm"
include "matring.mm"
include "ancoms.mm"
include "cbs.mm"
include "cfv.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "ringidcl.mm"
include "syl.mm"

theorem mat1bas
  let cA: class A
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let cN: class N
  assume mat1bas.a: |- A = ( N Mat R )
  assume mat1bas.b: |- B = ( Base ` A )
  assume mat1bas.i: |- .1. = ( 1r ` ( N Mat R ) )


  assert |- ( ( R e. Ring /\ N e. Fin ) -> .1. e. B )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    cN
    cR
    cmat
    co
    #
    crg
    wcel
    #
    c.1
    cB
    wcel
    @1
    @0
    @3
    @2
    cR
    cN
    @2
    eqid
    matring
    ancoms
    cB
    @2
    c.1
    cB
    cA
    cbs
    cfv
    @2
    cbs
    cfv
    mat1bas.b
    cA
    @2
    cbs
    mat1bas.a
    fveq2i
    eqtri
    mat1bas.i
    ringidcl
    syl
end
