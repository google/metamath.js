include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "ovres.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "jctil.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "sspnv.mm"
include "ffn.mm"
include "3syl.mm"
include "cba.mm"
include "cfv.mm"
include "wss.mm"
include "syl.mm"
include "adantr.mm"
include "sspba.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "eqfnov.mm"
include "mpbird.mm"

theorem sspmlem
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  assume sspmlem.y: |- Y = ( BaseSet ` W )
  assume sspmlem.h: |- H = ( SubSp ` U )
  assume sspmlem.1: |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( x e. Y /\ y e. Y ) ) -> ( x F y ) = ( x G y ) )
  assume sspmlem.2: |- ( W e. NrmCVec -> F : ( Y X. Y ) --> R )
  assume sspmlem.3: |- ( U e. NrmCVec -> G : ( ( BaseSet ` U ) X. ( BaseSet ` U ) ) --> S )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint U x
  disjoint U y
  disjoint W x
  disjoint W y
  disjoint Y x
  disjoint Y y
  assert |- ( ( U e. NrmCVec /\ W e. H ) -> F = ( G |` ( Y X. Y ) ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cG
    cY
    cY
    cxp
    #
    cres
    #
    wceq
    #
    @3
    @3
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    @7
    @8
    @4
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cY
    wral
    #
    wa
    #
    @2
    @12
    @6
    @2
    @11
    vx
    vy
    cY
    cY
    @2
    @7
    cY
    wcel
    @8
    cY
    wcel
    wa
    #
    wa
    @9
    @7
    @8
    cG
    co
    #
    @10
    sspmlem.1
    @14
    @10
    @15
    wceq
    @2
    @7
    @8
    cY
    cY
    cG
    ovres
    adantl
    eqtr4d
    ralrimivva
    @3
    eqid
    jctil
    @2
    cF
    @3
    wfn
    #
    @4
    @3
    wfn
    #
    @5
    @13
    wb
    @2
    cW
    cnv
    wcel
    @3
    cR
    cF
    wf
    @16
    cU
    cH
    cW
    sspmlem.h
    sspnv
    sspmlem.2
    @3
    cR
    cF
    ffn
    3syl
    @2
    cG
    cU
    cba
    cfv
    #
    @18
    cxp
    #
    wfn
    #
    @3
    @19
    wss
    #
    @17
    @0
    @20
    @1
    @0
    @19
    cS
    cG
    wf
    @20
    sspmlem.3
    @19
    cS
    cG
    ffn
    syl
    adantr
    @2
    cY
    @18
    wss
    #
    @22
    @21
    cU
    cH
    cW
    @18
    cY
    @18
    eqid
    sspmlem.y
    sspmlem.h
    sspba
    #
    @23
    cY
    @18
    cY
    @18
    xpss12
    syl2anc
    @19
    @3
    cG
    fnssres
    syl2anc
    vx
    vy
    cY
    cY
    cY
    cY
    cF
    @4
    eqfnov
    syl2anc
    mpbird
end
