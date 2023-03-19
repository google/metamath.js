include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cmat.mm"
include "co.mm"
include "cur.mm"
include "cbs.mm"
include "eqid.mm"
include "mat2pmat1.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "ancoms.mm"

theorem idmatidpmat
  let cP: class P
  let cR: class R
  let cT: class T
  let c.1: class .1.
  let cI: class I
  let cN: class N
  assume idmatidpmat.t: |- T = ( N matToPolyMat R )
  assume idmatidpmat.p: |- P = ( Poly1 ` R )
  assume idmatidpmat.1: |- .1. = ( 1r ` ( N Mat R ) )
  assume idmatidpmat.i: |- I = ( 1r ` ( N Mat P ) )


  assert |- ( ( R e. Ring /\ N e. Fin ) -> ( T ` .1. ) = I )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    c.1
    cT
    cfv
    #
    cI
    wceq
    @0
    @1
    wa
    cN
    cR
    cmat
    co
    #
    cur
    cfv
    #
    cT
    cfv
    cN
    cP
    cmat
    co
    #
    cur
    cfv
    @2
    cI
    @3
    @3
    cbs
    cfv
    #
    @5
    cP
    cR
    cT
    @5
    cbs
    cfv
    #
    cN
    idmatidpmat.t
    @3
    eqid
    @6
    eqid
    idmatidpmat.p
    @5
    eqid
    @7
    eqid
    mat2pmat1
    c.1
    @4
    cT
    idmatidpmat.1
    fveq2i
    idmatidpmat.i
    3eqtr4g
    ancoms
end
