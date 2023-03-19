include "cmul.mm"
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
include "mulcncf.mm"
include "eqeltrd.mm"

theorem mulcncff
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume mulcncff.f: |- ( ph -> F e. ( X -cn-> CC ) )
  assume mulcncff.g: |- ( ph -> G e. ( X -cn-> CC ) )


  assert |- ( ph -> ( F oF x. G ) e. ( X -cn-> CC ) )

  proof
    wph
    cF
    cG
    cmul
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
    cmul
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
    cmul
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
    mulcncff.f
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
    mulcncff.f
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
    mulcncff.g
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
    mulcncff.f
    eqeltrrd
    wph
    cG
    vx
    cX
    @2
    cmpt
    @3
    @8
    mulcncff.g
    eqeltrrd
    mulcncf
    eqeltrd
end
