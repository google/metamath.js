include "clvec.mm"
include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "cbs.mm"
include "csn.mm"
include "cdif.mm"
include "clspn.mm"
include "wn.mm"
include "wral.mm"
include "simpl.mm"
include "eqid.mm"
include "linds1.mm"
include "adantl.mm"
include "clmod.mm"
include "csca.mm"
include "cnzr.mm"
include "lveclmod.mm"
include "ad2antrr.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "drngnzr.mm"
include "syl.mm"
include "simplr.mm"
include "simpr.mm"
include "lindsind2.mm"
include "syl211anc.mm"
include "ralrimiva.mm"
include "lbsext.mm"
include "syl3anc.mm"
include "ex.mm"
include "lbslinds.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "lindsss.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem islinds4
  let cJ: class J
  let cW: class W
  let cY: class Y
  let vb: setvar b
  let vx: setvar x
  assume islinds4.j: |- J = ( LBasis ` W )

  disjoint J b
  disjoint W b
  disjoint Y b
  disjoint W x
  disjoint b x
  disjoint Y x
  assert |- ( W e. LVec -> ( Y e. ( LIndS ` W ) <-> E. b e. J Y C_ b ) )

  proof
    cW
    clvec
    wcel
    #
    cY
    cW
    clinds
    cfv
    #
    wcel
    #
    cY
    vb
    cv
    #
    wss
    #
    vb
    cJ
    wrex
    #
    @0
    @2
    @5
    @0
    @2
    wa
    #
    @0
    cY
    cW
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    cY
    @9
    csn
    cdif
    cW
    clspn
    cfv
    #
    cfv
    wcel
    wn
    #
    vx
    cY
    wral
    @5
    @0
    @2
    simpl
    @2
    @8
    @0
    @7
    cW
    cY
    @7
    eqid
    #
    linds1
    adantl
    @6
    @11
    vx
    cY
    @6
    @9
    cY
    wcel
    #
    wa
    cW
    clmod
    wcel
    #
    cW
    csca
    cfv
    #
    cnzr
    wcel
    #
    @2
    @13
    @11
    @0
    @14
    @2
    @13
    cW
    lveclmod
    #
    ad2antrr
    @0
    @16
    @2
    @13
    @0
    @15
    cdr
    wcel
    @16
    @15
    cW
    @15
    eqid
    #
    lvecdrng
    @15
    drngnzr
    syl
    ad2antrr
    @0
    @2
    @13
    simplr
    @6
    @13
    simpr
    @9
    cY
    @10
    @15
    cW
    @10
    eqid
    #
    @18
    lindsind2
    syl211anc
    ralrimiva
    vx
    cY
    cJ
    @10
    @7
    cW
    vb
    islinds4.j
    @12
    @19
    lbsext
    syl3anc
    ex
    @0
    @4
    @2
    vb
    cJ
    @0
    @3
    cJ
    wcel
    #
    wa
    #
    @4
    @2
    @21
    @4
    wa
    @14
    @3
    @1
    wcel
    #
    @4
    @2
    @0
    @14
    @20
    @4
    @17
    ad2antrr
    @20
    @22
    @0
    @4
    cJ
    @1
    @3
    cJ
    cW
    islinds4.j
    lbslinds
    sseli
    ad2antlr
    @21
    @4
    simpr
    @3
    cY
    cW
    lindsss
    syl3anc
    ex
    rexlimdva
    impbid
end
