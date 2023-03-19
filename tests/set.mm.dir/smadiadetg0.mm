include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cmdat.mm"
include "cmulr.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "smadiadetg.mm"

theorem smadiadetg0
  let cR: class R
  let cS: class S
  let cK: class K
  let cM: class M
  let cN: class N
  assume smadiadetg0.r: |- R e. CRing


  assert |- ( ( M e. ( Base ` ( N Mat R ) ) /\ K e. N /\ S e. ( Base ` R ) ) -> ( ( N maDet R ) ` ( K ( M ( N matRRep R ) S ) K ) ) = ( S ( .r ` R ) ( ( ( N \ { K } ) maDet R ) ` ( K ( ( N subMat R ) ` M ) K ) ) ) )

  proof
    cN
    cR
    cmat
    co
    #
    @0
    cbs
    cfv
    #
    cN
    cR
    cmdat
    co
    #
    cR
    cS
    cR
    cmulr
    cfv
    #
    cN
    cK
    csn
    cdif
    cR
    cmdat
    co
    #
    cK
    cM
    cN
    @0
    eqid
    @1
    eqid
    smadiadetg0.r
    @2
    eqid
    @4
    eqid
    @3
    eqid
    smadiadetg
end
