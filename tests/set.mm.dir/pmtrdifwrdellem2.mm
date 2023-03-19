include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cpmtr.mm"
include "wral.mm"
include "wfn.mm"
include "wceq.mm"
include "wa.mm"
include "wrdsymbcl.mm"
include "eqid.mm"
include "pmtrdifellem1.mm"
include "syl.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "hashfn.mm"
include "3syl.mm"
include "cn0.mm"
include "lencl.mm"
include "hashfzo0.mm"
include "eqtr2d.mm"

theorem pmtrdifwrdellem2
  let vx: setvar x
  let cR: class R
  let cT: class T
  let cU: class U
  let cK: class K
  let cN: class N
  let cW: class W
  let vr: setvar r
  let vt: setvar t
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifwrdel.0: |- U = ( x e. ( 0 ..^ ( # ` W ) ) |-> ( ( pmTrsp ` N ) ` dom ( ( W ` x ) \ _I ) ) )

  disjoint R x
  disjoint W x
  disjoint N x
  disjoint T x
  disjoint r t
  disjoint r x
  disjoint t x
  disjoint K r
  disjoint N r
  disjoint R r
  assert |- ( W e. Word T -> ( # ` W ) = ( # ` U ) )

  proof
    cW
    cT
    cword
    wcel
    #
    cU
    chash
    cfv
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    chash
    cfv
    #
    @2
    @0
    vx
    cv
    #
    cW
    cfv
    #
    cid
    cdif
    cdm
    cN
    cpmtr
    cfv
    cfv
    #
    cR
    wcel
    #
    vx
    @3
    wral
    cU
    @3
    wfn
    @1
    @4
    wceq
    @0
    @8
    vx
    @3
    @0
    @5
    @3
    wcel
    wa
    @6
    cT
    wcel
    @8
    @5
    cT
    cW
    wrdsymbcl
    @6
    cR
    @7
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @7
    eqid
    pmtrdifellem1
    syl
    ralrimiva
    vx
    @3
    @7
    cU
    cR
    pmtrdifwrdel.0
    fnmpt
    @3
    cU
    hashfn
    3syl
    @0
    @2
    cn0
    wcel
    @4
    @2
    wceq
    cT
    cW
    lencl
    @2
    hashfzo0
    syl
    eqtr2d
end
