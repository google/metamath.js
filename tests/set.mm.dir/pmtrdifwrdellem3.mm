include "cword.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "cpmtr.mm"
include "wrdsymbcl.mm"
include "eqid.mm"
include "pmtrdifellem3.mm"
include "syl.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "weq.mm"
include "fveq2.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "simpr.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "ralrimiva.mm"

theorem pmtrdifwrdellem3
  let vx: setvar x
  let cR: class R
  let cT: class T
  let cU: class U
  let vi: setvar i
  let vn: setvar n
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
  disjoint T i
  disjoint T n
  disjoint i n
  disjoint W i
  disjoint W n
  disjoint i x
  disjoint N x
  disjoint T x
  disjoint r t
  disjoint r x
  disjoint t x
  disjoint K r
  disjoint N r
  disjoint R r
  assert |- ( W e. Word T -> A. i e. ( 0 ..^ ( # ` W ) ) A. n e. ( N \ { K } ) ( ( W ` i ) ` n ) = ( ( U ` i ) ` n ) )

  proof
    cW
    cT
    cword
    wcel
    #
    vn
    cv
    #
    vi
    cv
    #
    cW
    cfv
    #
    cfv
    #
    @1
    @2
    cU
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cN
    cK
    csn
    cdif
    #
    wral
    #
    vi
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    @0
    @2
    @10
    wcel
    #
    wa
    #
    @9
    @4
    @1
    @3
    cid
    cdif
    #
    cdm
    #
    cN
    cpmtr
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    @8
    wral
    #
    @12
    @3
    cT
    wcel
    @19
    @2
    cT
    cW
    wrdsymbcl
    vn
    @3
    cR
    @16
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @16
    eqid
    pmtrdifellem3
    syl
    @12
    @7
    @18
    vn
    @8
    @12
    @6
    @17
    @4
    @12
    @1
    @5
    @16
    @12
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
    #
    cdm
    #
    @15
    cfv
    #
    @16
    @10
    cU
    cvv
    cU
    vx
    @10
    @24
    cmpt
    wceq
    @12
    pmtrdifwrdel.0
    a1i
    vx
    vi
    weq
    #
    @24
    @16
    wceq
    @12
    @25
    @23
    @14
    @15
    @25
    @22
    @13
    @25
    @21
    @3
    cid
    @20
    @2
    cW
    fveq2
    difeq1d
    dmeqd
    fveq2d
    adantl
    @0
    @11
    simpr
    @12
    @14
    @15
    fvexd
    fvmptd
    fveq1d
    eqeq2d
    ralbidv
    mpbird
    ralrimiva
end
