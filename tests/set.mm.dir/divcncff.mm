include "cdiv.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cvv.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
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
include "divcncf.mm"
include "eqeltrd.mm"

theorem divcncff
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vk: setvar k
  assume divcncff.f: |- ( ph -> F e. ( X -cn-> CC ) )
  assume divcncff.g: |- ( ph -> G e. ( X -cn-> ( CC \ { 0 } ) ) )


  assert |- ( ph -> ( F oF / G ) e. ( X -cn-> CC ) )

  proof
    wph
    cF
    cG
    cdiv
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
    cdiv
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
    cdiv
    cF
    cG
    cvv
    cc
    cc
    cc0
    csn
    cdif
    #
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
    divcncff.f
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
    @5
    cX
    cc
    cF
    wf
    divcncff.f
    cX
    cc
    cF
    cncff
    syl
    #
    ffvelrnda
    wph
    cX
    @4
    @0
    cG
    wph
    cG
    cX
    @4
    ccncf
    co
    #
    wcel
    cX
    @4
    cG
    wf
    divcncff.g
    cX
    @4
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
    @6
    feqmptd
    #
    wph
    vx
    cX
    @4
    cG
    @8
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
    @9
    divcncff.f
    eqeltrrd
    wph
    cG
    vx
    cX
    @2
    cmpt
    @7
    @10
    divcncff.g
    eqeltrrd
    divcncf
    eqeltrd
end
