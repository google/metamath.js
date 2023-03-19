include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cpmtr.mm"
include "wa.mm"
include "wrdsymbcl.mm"
include "eqid.mm"
include "pmtrdifellem1.mm"
include "syl.mm"
include "fmptd.mm"
include "iswrdi.mm"

theorem pmtrdifwrdellem1
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
  assert |- ( W e. Word T -> U e. Word R )

  proof
    cW
    cT
    cword
    wcel
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cR
    cU
    wf
    cU
    cR
    cword
    wcel
    @0
    vx
    @2
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
    cU
    @0
    @3
    @2
    wcel
    wa
    @4
    cT
    wcel
    @5
    cR
    wcel
    @3
    cT
    cW
    wrdsymbcl
    @4
    cR
    @5
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @5
    eqid
    pmtrdifellem1
    syl
    pmtrdifwrdel.0
    fmptd
    cR
    @1
    cU
    iswrdi
    syl
end
