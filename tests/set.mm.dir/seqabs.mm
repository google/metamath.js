include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "cabs.mm"
include "caddc.mm"
include "cseq.mm"
include "cle.mm"
include "fzfid.mm"
include "fsumabs.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "fsumser.mm"
include "fveq2d.mm"
include "cc.mm"
include "abscl.mm"
include "recnd.mm"
include "syl.mm"
include "3brtr3d.mm"

theorem seqabs
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume seqabs.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqabs.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. CC )
  assume seqabs.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( G ` k ) = ( abs ` ( F ` k ) ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( abs ` ( seq M ( + , F ) ` N ) ) <_ ( seq M ( + , G ) ` N ) )

  proof
    wph
    cM
    cN
    cfz
    co
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    @0
    @2
    cabs
    cfv
    #
    vk
    csu
    cN
    caddc
    cF
    cM
    cseq
    cfv
    #
    cabs
    cfv
    cN
    caddc
    cG
    cM
    cseq
    cfv
    cle
    wph
    @0
    @2
    vk
    wph
    cM
    cN
    fzfid
    seqabs.2
    fsumabs
    wph
    @3
    @5
    cabs
    wph
    @2
    vk
    cF
    cM
    cN
    wph
    @1
    @0
    wcel
    wa
    #
    @2
    eqidd
    seqabs.1
    seqabs.2
    fsumser
    fveq2d
    wph
    @4
    vk
    cG
    cM
    cN
    seqabs.3
    seqabs.1
    @6
    @2
    cc
    wcel
    #
    @4
    cc
    wcel
    seqabs.2
    @7
    @4
    @2
    abscl
    recnd
    syl
    fsumser
    3brtr3d
end
