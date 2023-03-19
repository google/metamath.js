include "clsi.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cneg.mm"
include "clsp.mm"
include "cxne.mm"
include "cr.mm"
include "nfcv.mm"
include "feqmptdf.mm"
include "fveq2d.mm"
include "ffvelrnda.mm"
include "liminfvaluz2.mm"
include "eqtrd.mm"

theorem liminfvaluz4
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume liminfvaluz4.1: |- F/ k ph
  assume liminfvaluz4.2: |- F/_ k F
  assume liminfvaluz4.3: |- ( ph -> M e. ZZ )
  assume liminfvaluz4.4: |- Z = ( ZZ>= ` M )
  assume liminfvaluz4.5: |- ( ph -> F : Z --> RR )

  disjoint M k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = -e ( limsup ` ( k e. Z |-> -u ( F ` k ) ) ) )

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
    cneg
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
    cr
    cF
    vk
    cZ
    nfcv
    liminfvaluz4.2
    liminfvaluz4.5
    feqmptdf
    fveq2d
    wph
    @1
    vk
    cM
    cZ
    liminfvaluz4.1
    liminfvaluz4.3
    liminfvaluz4.4
    wph
    cZ
    cr
    @0
    cF
    liminfvaluz4.5
    ffvelrnda
    liminfvaluz2
    eqtrd
end
