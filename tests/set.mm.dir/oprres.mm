include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "3expb.mm"
include "ovres.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "jctil.mm"
include "wfn.mm"
include "wb.mm"
include "ffnd.mm"
include "wss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "eqfnov.mm"
include "mpbird.mm"

theorem oprres
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  assume oprres.v: |- ( ( ph /\ x e. Y /\ y e. Y ) -> ( x F y ) = ( x G y ) )
  assume oprres.s: |- ( ph -> Y C_ X )
  assume oprres.f: |- ( ph -> F : ( Y X. Y ) --> R )
  assume oprres.g: |- ( ph -> G : ( X X. X ) --> S )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> F = ( G |` ( Y X. Y ) ) )

  proof
    wph
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
    @0
    @0
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
    @4
    @5
    @1
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
    wph
    @9
    @3
    wph
    @8
    vx
    vy
    cY
    cY
    wph
    @4
    cY
    wcel
    #
    @5
    cY
    wcel
    #
    wa
    #
    wa
    @6
    @4
    @5
    cG
    co
    #
    @7
    wph
    @11
    @12
    @6
    @14
    wceq
    oprres.v
    3expb
    @13
    @7
    @14
    wceq
    wph
    @4
    @5
    cY
    cY
    cG
    ovres
    adantl
    eqtr4d
    ralrimivva
    @0
    eqid
    jctil
    wph
    cF
    @0
    wfn
    @1
    @0
    wfn
    #
    @2
    @10
    wb
    wph
    @0
    cR
    cF
    oprres.f
    ffnd
    wph
    cG
    cX
    cX
    cxp
    #
    wfn
    @0
    @16
    wss
    #
    @15
    wph
    @16
    cS
    cG
    oprres.g
    ffnd
    wph
    cY
    cX
    wss
    #
    @18
    @17
    oprres.s
    oprres.s
    cY
    cX
    cY
    cX
    xpss12
    syl2anc
    @16
    @0
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
    @1
    eqfnov
    syl2anc
    mpbird
end
