include "csu.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "cuz.mm"
include "eqid.mm"
include "wcel.mm"
include "cz.mm"
include "eluzel2.mm"
include "syl.mm"
include "cfz.mm"
include "co.mm"
include "fzssuz.mm"
include "syl6ss.mm"
include "zsum.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "cdm.mm"
include "cc.mm"
include "wf.mm"
include "fclim.mm"
include "ffun.mm"
include "ax-mp.mm"
include "fsumcvg2.mm"
include "funbrfv.mm"
include "mpsyl.mm"
include "eqtrd.mm"

theorem fsumsers
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume fsumsers.1: |- ( ( ph /\ k e. ( ZZ>= ` M ) ) -> ( F ` k ) = if ( k e. A , B , 0 ) )
  assume fsumsers.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumsers.3: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume fsumsers.4: |- ( ph -> A C_ ( M ... N ) )

  disjoint A k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint M k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B m
  disjoint B n
  disjoint F n
  disjoint N m
  disjoint m ph
  disjoint n ph
  disjoint M m
  disjoint M n
  assert |- ( ph -> sum_ k e. A B = ( seq M ( + , F ) ` N ) )

  proof
    wph
    cA
    cB
    vk
    csu
    caddc
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    cN
    @0
    cfv
    #
    wph
    cA
    cB
    vk
    cF
    cM
    cM
    cuz
    cfv
    #
    @3
    eqid
    wph
    cN
    @3
    wcel
    cM
    cz
    wcel
    fsumsers.2
    cM
    cN
    eluzel2
    syl
    wph
    cA
    cM
    cN
    cfz
    co
    @3
    fsumsers.4
    cM
    cN
    fzssuz
    syl6ss
    fsumsers.1
    fsumsers.3
    zsum
    cli
    wfun
    #
    wph
    @0
    @2
    cli
    wbr
    @1
    @2
    wceq
    cli
    cdm
    #
    cc
    cli
    wf
    @4
    fclim
    @5
    cc
    cli
    ffun
    ax-mp
    wph
    cA
    cB
    vk
    cF
    cM
    cN
    fsumsers.1
    fsumsers.2
    fsumsers.3
    fsumsers.4
    fsumcvg2
    @0
    @2
    cli
    funbrfv
    mpsyl
    eqtrd
end
