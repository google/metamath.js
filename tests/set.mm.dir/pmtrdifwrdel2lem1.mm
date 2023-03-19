include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cpmtr.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "weq.mm"
include "fveq2.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "fveq2d.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "fveq1d.mm"
include "wrdsymbcl.mm"
include "adantlr.mm"
include "simplr.mm"
include "eqid.mm"
include "pmtrdifellem4.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ralrimiva.mm"

theorem pmtrdifwrdel2lem1
  let vx: setvar x
  let cR: class R
  let cT: class T
  let cU: class U
  let vi: setvar i
  let cK: class K
  let cN: class N
  let cW: class W
  let vn: setvar n
  let vr: setvar r
  let vt: setvar t
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifwrdel.0: |- U = ( x e. ( 0 ..^ ( # ` W ) ) |-> ( ( pmTrsp ` N ) ` dom ( ( W ` x ) \ _I ) ) )

  disjoint R x
  disjoint W x
  disjoint T i
  disjoint W i
  disjoint i x
  disjoint K i
  disjoint N i
  disjoint N x
  disjoint T x
  disjoint T n
  disjoint i n
  disjoint W n
  disjoint r t
  disjoint r x
  disjoint t x
  disjoint K r
  disjoint N r
  disjoint R r
  assert |- ( ( W e. Word T /\ K e. N ) -> A. i e. ( 0 ..^ ( # ` W ) ) ( ( U ` i ) ` K ) = K )

  proof
    cW
    cT
    cword
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cK
    vi
    cv
    #
    cU
    cfv
    #
    cfv
    #
    cK
    wceq
    vi
    cc0
    cW
    chash
    cfv
    cfzo
    co
    #
    @2
    @3
    @6
    wcel
    #
    wa
    #
    @5
    cK
    @3
    cW
    cfv
    #
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
    cK
    @8
    cK
    @4
    @13
    @8
    @7
    @13
    cvv
    wcel
    @4
    @13
    wceq
    @2
    @7
    simpr
    @11
    @12
    fvex
    vx
    @3
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
    @12
    cfv
    @13
    @6
    cvv
    cU
    vx
    vi
    weq
    #
    @18
    @11
    @12
    @19
    @17
    @10
    @19
    @16
    @9
    cid
    @15
    @3
    cW
    fveq2
    difeq1d
    dmeqd
    fveq2d
    pmtrdifwrdel.0
    fvmptg
    sylancl
    fveq1d
    @8
    @9
    cT
    wcel
    #
    @1
    @14
    cK
    wceq
    @0
    @7
    @20
    @1
    @3
    cT
    cW
    wrdsymbcl
    adantlr
    @0
    @1
    @7
    simplr
    @9
    cR
    @13
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @13
    eqid
    pmtrdifellem4
    syl2anc
    eqtrd
    ralrimiva
end
