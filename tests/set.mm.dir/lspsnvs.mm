include "clvec.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "csn.mm"
include "cfv.mm"
include "clmod.mm"
include "wss.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3.mm"
include "lspsnvsi.mm"
include "syl3anc.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cur.mm"
include "cdr.mm"
include "wceq.mm"
include "lvecdrng.mm"
include "simp2r.mm"
include "eqid.mm"
include "drnginvrl.mm"
include "oveq1d.mm"
include "drnginvrcl.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "lmodvscl.mm"
include "eqsstr3d.mm"
include "eqssd.mm"

theorem lspsnvs
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lspsnvs.v: |- V = ( Base ` W )
  assume lspsnvs.f: |- F = ( Scalar ` W )
  assume lspsnvs.t: |- .x. = ( .s ` W )
  assume lspsnvs.k: |- K = ( Base ` F )
  assume lspsnvs.o: |- .0. = ( 0g ` F )
  assume lspsnvs.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LVec /\ ( R e. K /\ R =/= .0. ) /\ X e. V ) -> ( N ` { ( R .x. X ) } ) = ( N ` { X } ) )

  proof
    cW
    clvec
    wcel
    #
    cR
    cK
    wcel
    #
    cR
    c.0
    wne
    #
    wa
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cR
    cX
    c.x
    co
    #
    csn
    cN
    cfv
    #
    cX
    csn
    #
    cN
    cfv
    #
    @5
    cW
    clmod
    wcel
    #
    @1
    @4
    @7
    @9
    wss
    @0
    @3
    @10
    @4
    cW
    lveclmod
    3ad2ant1
    #
    @0
    @1
    @2
    @4
    simp2l
    #
    @0
    @3
    @4
    simp3
    #
    cR
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lspsnvs.f
    lspsnvs.k
    lspsnvs.v
    lspsnvs.t
    lspsnvs.n
    lspsnvsi
    syl3anc
    @5
    @9
    cR
    cF
    cinvr
    cfv
    #
    cfv
    #
    @6
    c.x
    co
    #
    csn
    #
    cN
    cfv
    #
    @7
    @5
    @17
    @8
    cN
    @5
    @16
    cX
    @5
    @15
    cR
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cF
    cur
    cfv
    #
    cX
    c.x
    co
    #
    @16
    cX
    @5
    @20
    @22
    cX
    c.x
    @5
    cF
    cdr
    wcel
    #
    @1
    @2
    @20
    @22
    wceq
    @0
    @3
    @24
    @4
    cF
    cW
    lspsnvs.f
    lvecdrng
    3ad2ant1
    #
    @12
    @0
    @1
    @2
    @4
    simp2r
    #
    cK
    cF
    @19
    @22
    @14
    cR
    c.0
    lspsnvs.k
    lspsnvs.o
    @19
    eqid
    #
    @22
    eqid
    #
    @14
    eqid
    #
    drnginvrl
    syl3anc
    oveq1d
    @5
    @10
    @15
    cK
    wcel
    #
    @1
    @4
    @21
    @16
    wceq
    @11
    @5
    @24
    @1
    @2
    @30
    @25
    @12
    @26
    cK
    cF
    @14
    cR
    c.0
    lspsnvs.k
    lspsnvs.o
    @29
    drnginvrcl
    syl3anc
    #
    @12
    @13
    @15
    cR
    c.x
    @19
    cF
    cK
    cV
    cW
    cX
    lspsnvs.v
    lspsnvs.f
    lspsnvs.t
    lspsnvs.k
    @27
    lmodvsass
    syl13anc
    @5
    @10
    @4
    @23
    cX
    wceq
    @11
    @13
    c.x
    @22
    cF
    cV
    cW
    cX
    lspsnvs.v
    lspsnvs.f
    lspsnvs.t
    @28
    lmodvs1
    syl2anc
    3eqtr3d
    sneqd
    fveq2d
    @5
    @10
    @30
    @6
    cV
    wcel
    #
    @18
    @7
    wss
    @11
    @31
    @5
    @10
    @1
    @4
    @32
    @11
    @12
    @13
    cR
    c.x
    cF
    cK
    cV
    cW
    cX
    lspsnvs.v
    lspsnvs.f
    lspsnvs.t
    lspsnvs.k
    lmodvscl
    syl3anc
    @15
    c.x
    cF
    cK
    cN
    cV
    cW
    @6
    lspsnvs.f
    lspsnvs.k
    lspsnvs.v
    lspsnvs.t
    lspsnvs.n
    lspsnvsi
    syl3anc
    eqsstr3d
    eqssd
end
