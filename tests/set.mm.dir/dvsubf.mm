include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cof.mm"
include "cc.mm"
include "ffvelrnda.mm"
include "cdm.mm"
include "wf.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "dvfg.mm"
include "syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "dvmptsub.mm"
include "cvv.mm"
include "ovex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "offval2.mm"
include "3eqtr4d.mm"

theorem dvsubf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume dvsubf.s: |- ( ph -> S e. { RR , CC } )
  assume dvsubf.f: |- ( ph -> F : X --> CC )
  assume dvsubf.g: |- ( ph -> G : X --> CC )
  assume dvsubf.fdv: |- ( ph -> dom ( S _D F ) = X )
  assume dvsubf.gdv: |- ( ph -> dom ( S _D G ) = X )


  assert |- ( ph -> ( S _D ( F oF - G ) ) = ( ( S _D F ) oF - ( S _D G ) ) )

  proof
    wph
    cS
    vx
    cX
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cmin
    co
    cmpt
    #
    cdv
    co
    vx
    cX
    @0
    cS
    cF
    cdv
    co
    #
    cfv
    #
    @0
    cS
    cG
    cdv
    co
    #
    cfv
    #
    cmin
    co
    cmpt
    cS
    cF
    cG
    cmin
    cof
    #
    co
    #
    cdv
    co
    @4
    @6
    @8
    co
    wph
    vx
    @1
    @5
    @2
    @7
    cS
    cc
    cc
    cX
    dvsubf.s
    wph
    cX
    cc
    @0
    cF
    dvsubf.f
    ffvelrnda
    #
    wph
    cX
    cc
    @0
    @4
    wph
    @4
    cdm
    #
    cc
    @4
    wf
    #
    cX
    cc
    @4
    wf
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @12
    dvsubf.s
    cS
    cF
    dvfg
    syl
    wph
    @11
    cX
    cc
    @4
    dvsubf.fdv
    feq2d
    mpbid
    #
    ffvelrnda
    #
    wph
    @4
    cS
    vx
    cX
    @1
    cmpt
    #
    cdv
    co
    vx
    cX
    @5
    cmpt
    wph
    cF
    @16
    cS
    cdv
    wph
    vx
    cX
    cc
    cF
    dvsubf.f
    feqmptd
    #
    oveq2d
    wph
    vx
    cX
    cc
    @4
    @14
    feqmptd
    #
    eqtr3d
    wph
    cX
    cc
    @0
    cG
    dvsubf.g
    ffvelrnda
    #
    wph
    cX
    cc
    @0
    @6
    wph
    @6
    cdm
    #
    cc
    @6
    wf
    #
    cX
    cc
    @6
    wf
    wph
    @13
    @21
    dvsubf.s
    cS
    cG
    dvfg
    syl
    wph
    @20
    cX
    cc
    @6
    dvsubf.gdv
    feq2d
    mpbid
    #
    ffvelrnda
    #
    wph
    @6
    cS
    vx
    cX
    @2
    cmpt
    #
    cdv
    co
    vx
    cX
    @7
    cmpt
    wph
    cG
    @24
    cS
    cdv
    wph
    vx
    cX
    cc
    cG
    dvsubf.g
    feqmptd
    #
    oveq2d
    wph
    vx
    cX
    cc
    @6
    @22
    feqmptd
    #
    eqtr3d
    dvmptsub
    wph
    @9
    @3
    cS
    cdv
    wph
    vx
    cX
    @1
    @2
    cmin
    cF
    cG
    cvv
    cc
    cc
    wph
    cX
    @11
    cvv
    dvsubf.fdv
    @4
    cS
    cF
    cdv
    ovex
    dmex
    syl6eqelr
    #
    @10
    @19
    @17
    @25
    offval2
    oveq2d
    wph
    vx
    cX
    @5
    @7
    cmin
    @4
    @6
    cvv
    cc
    cc
    @27
    @15
    @23
    @18
    @26
    offval2
    3eqtr4d
end
