include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cmat.mm"
include "co.mm"
include "cghm.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "eqid.mm"
include "mat2pmatghm.mm"
include "ancoms.mm"
include "ghmid.mm"
include "syl.mm"

theorem 0mat2pmat
  let cP: class P
  let cR: class R
  let cT: class T
  let cN: class N
  let c.0: class .0.
  let cZ: class Z
  assume idmatidpmat.t: |- T = ( N matToPolyMat R )
  assume idmatidpmat.p: |- P = ( Poly1 ` R )
  assume 0mat2pmat.0: |- .0. = ( 0g ` ( N Mat R ) )
  assume 0mat2pmat.z: |- Z = ( 0g ` ( N Mat P ) )


  assert |- ( ( R e. Ring /\ N e. Fin ) -> ( T ` .0. ) = Z )

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
    cT
    cN
    cR
    cmat
    co
    #
    cN
    cP
    cmat
    co
    #
    cghm
    co
    wcel
    #
    c.0
    cT
    cfv
    cZ
    wceq
    @1
    @0
    @4
    @2
    @2
    cbs
    cfv
    #
    @3
    cP
    cR
    cT
    @3
    cbs
    cfv
    #
    cN
    idmatidpmat.t
    @2
    eqid
    @5
    eqid
    idmatidpmat.p
    @3
    eqid
    @6
    eqid
    mat2pmatghm
    ancoms
    @2
    @3
    cT
    c.0
    cZ
    0mat2pmat.0
    0mat2pmat.z
    ghmid
    syl
end
