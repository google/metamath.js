include "clsi.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cxne.mm"
include "clsp.mm"
include "cxr.mm"
include "nfcv.mm"
include "feqmptdf.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "liminfvaluz.mm"
include "eqtrd.mm"

theorem liminfvaluz3
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume liminfvaluz3.1: |- F/ k ph
  assume liminfvaluz3.2: |- F/_ k F
  assume liminfvaluz3.3: |- ( ph -> M e. ZZ )
  assume liminfvaluz3.4: |- Z = ( ZZ>= ` M )
  assume liminfvaluz3.5: |- ( ph -> F : Z --> RR* )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = -e ( limsup ` ( k e. Z |-> -e ( F ` k ) ) ) )

  proof
    wph
    cF
    clsi
    cfv
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    clsi
    cfv
    vk
    cZ
    @1
    cxne
    cmpt
    clsp
    cfv
    cxne
    wph
    cF
    @2
    clsi
    wph
    vk
    cZ
    cxr
    cF
    vk
    cZ
    nfcv
    liminfvaluz3.2
    liminfvaluz3.5
    feqmptdf
    fveq2d
    wph
    @1
    vk
    cM
    cZ
    liminfvaluz3.1
    liminfvaluz3.3
    liminfvaluz3.4
    wph
    cZ
    cxr
    @0
    cF
    liminfvaluz3.5
    ffvelrnda
    liminfvaluz
    eqtrd
end
