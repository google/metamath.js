include "csn.mm"
include "cv.mm"
include "wpss.mm"
include "cfv.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "wcel.mm"
include "wss.mm"
include "wne.mm"
include "df-pss.mm"
include "simpr.mm"
include "nesym.mm"
include "sylib.mm"
include "sylbi.mm"
include "clvec.mm"
include "wo.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "lspsnat.mm"
include "syl31anc.mm"
include "orcomd.mm"
include "ord.mm"
include "ex.mm"
include "com23.mm"
include "npss.mm"
include "syl6ibr.mm"
include "syl5.mm"
include "ralrimiva.mm"
include "ralinexa.mm"

theorem lspsncv0
  let wph: wff ph
  let vy: setvar y
  let cS: class S
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lspsncv0.v: |- V = ( Base ` W )
  assume lspsncv0.z: |- .0. = ( 0g ` W )
  assume lspsncv0.s: |- S = ( LSubSp ` W )
  assume lspsncv0.n: |- N = ( LSpan ` W )
  assume lspsncv0.w: |- ( ph -> W e. LVec )
  assume lspsncv0.x: |- ( ph -> X e. V )
  assume lspsncv0.e: |- ( ph -> X =/= .0. )

  disjoint ph y
  assert |- ( ph -> -. E. y e. S ( { .0. } C. y /\ y C. ( N ` { X } ) ) )

  proof
    wph
    c.0
    csn
    #
    vy
    cv
    #
    wpss
    #
    @1
    cX
    csn
    cN
    cfv
    #
    wpss
    #
    wn
    #
    wi
    #
    vy
    cS
    wral
    @2
    @4
    wa
    vy
    cS
    wrex
    wn
    wph
    @6
    vy
    cS
    @2
    @1
    @0
    wceq
    #
    wn
    #
    wph
    @1
    cS
    wcel
    #
    wa
    #
    @5
    @2
    @0
    @1
    wss
    #
    @0
    @1
    wne
    #
    wa
    #
    @8
    @0
    @1
    df-pss
    @13
    @12
    @8
    @11
    @12
    simpr
    @0
    @1
    nesym
    sylib
    sylbi
    @10
    @8
    @1
    @3
    wss
    #
    @1
    @3
    wceq
    #
    wi
    @5
    @10
    @14
    @8
    @15
    @10
    @14
    @8
    @15
    wi
    @10
    @14
    wa
    #
    @7
    @15
    @16
    @15
    @7
    @16
    cW
    clvec
    wcel
    #
    @9
    cX
    cV
    wcel
    #
    @14
    @15
    @7
    wo
    wph
    @17
    @9
    @14
    lspsncv0.w
    ad2antrr
    wph
    @9
    @14
    simplr
    wph
    @18
    @9
    @14
    lspsncv0.x
    ad2antrr
    @10
    @14
    simpr
    cS
    @1
    cN
    cV
    cW
    cX
    c.0
    lspsncv0.v
    lspsncv0.z
    lspsncv0.s
    lspsncv0.n
    lspsnat
    syl31anc
    orcomd
    ord
    ex
    com23
    @1
    @3
    npss
    syl6ibr
    syl5
    ralrimiva
    @2
    @4
    vy
    cS
    ralinexa
    sylib
end
