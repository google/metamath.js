include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cncfrss.mm"
include "cnex.mm"
include "ssex.mm"
include "3syl.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "offval2.mm"
include "eqeltrrd.mm"
include "addcncf.mm"
include "eqeltrd.mm"

theorem addcncff
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume addcncff.f: |- ( ph -> F e. ( X -cn-> CC ) )
  assume addcncff.g: |- ( ph -> G e. ( X -cn-> CC ) )


  assert |- ( ph -> ( F oF + G ) e. ( X -cn-> CC ) )

  proof
    wph
    cF
    cG
    caddc
    cof
    co
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
    caddc
    co
    cmpt
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cX
    @1
    @2
    caddc
    cF
    cG
    cvv
    cc
    cc
    wph
    cF
    @3
    wcel
    #
    cX
    cc
    wss
    cX
    cvv
    wcel
    addcncff.f
    cX
    cc
    cF
    cncfrss
    cX
    cc
    cnex
    ssex
    3syl
    wph
    cX
    cc
    @0
    cF
    wph
    @4
    cX
    cc
    cF
    wf
    addcncff.f
    cX
    cc
    cF
    cncff
    syl
    #
    ffvelrnda
    wph
    cX
    cc
    @0
    cG
    wph
    cG
    @3
    wcel
    cX
    cc
    cG
    wf
    addcncff.g
    cX
    cc
    cG
    cncff
    syl
    #
    ffvelrnda
    wph
    vx
    cX
    cc
    cF
    @5
    feqmptd
    #
    wph
    vx
    cX
    cc
    cG
    @6
    feqmptd
    #
    offval2
    wph
    vx
    @1
    @2
    cX
    wph
    cF
    vx
    cX
    @1
    cmpt
    @3
    @7
    addcncff.f
    eqeltrrd
    wph
    cG
    vx
    cX
    @2
    cmpt
    @3
    @8
    addcncff.g
    eqeltrrd
    addcncf
    eqeltrd
end
