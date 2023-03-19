include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cdv.mm"
include "cc.mm"
include "ccncf.mm"
include "wcel.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "dvsubf.mm"
include "subcncff.mm"
include "eqeltrd.mm"

theorem dvsubcncf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume dvsubcncf.s: |- ( ph -> S e. { RR , CC } )
  assume dvsubcncf.f: |- ( ph -> F : X --> CC )
  assume dvsubcncf.g: |- ( ph -> G : X --> CC )
  assume dvsubcncf.fdv: |- ( ph -> ( S _D F ) e. ( X -cn-> CC ) )
  assume dvsubcncf.gdv: |- ( ph -> ( S _D G ) e. ( X -cn-> CC ) )


  assert |- ( ph -> ( S _D ( F oF - G ) ) e. ( X -cn-> CC ) )

  proof
    wph
    cS
    cF
    cG
    cmin
    cof
    #
    co
    cdv
    co
    cS
    cF
    cdv
    co
    #
    cS
    cG
    cdv
    co
    #
    @0
    co
    cX
    cc
    ccncf
    co
    #
    wph
    cS
    cF
    cG
    cX
    dvsubcncf.s
    dvsubcncf.f
    dvsubcncf.g
    wph
    @1
    @3
    wcel
    cX
    cc
    @1
    wf
    @1
    cdm
    cX
    wceq
    dvsubcncf.fdv
    cX
    cc
    @1
    cncff
    cX
    cc
    @1
    fdm
    3syl
    wph
    @2
    @3
    wcel
    cX
    cc
    @2
    wf
    @2
    cdm
    cX
    wceq
    dvsubcncf.gdv
    cX
    cc
    @2
    cncff
    cX
    cc
    @2
    fdm
    3syl
    dvsubf
    wph
    @1
    @2
    cX
    dvsubcncf.fdv
    dvsubcncf.gdv
    subcncff
    eqeltrd
end
