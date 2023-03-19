include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzel2.mm"
include "syl.mm"
include "uzid.mm"
include "cseq.mm"
include "wceq.mm"
include "seq1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wral.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqtrd.mm"
include "c1.mm"
include "caddc.mm"
include "wss.mm"
include "fzp1ss.mm"
include "sselda.mm"
include "syldan.mm"
include "seqfveq2.mm"

theorem seqfveq
  let wph: wff ph
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume seqfveq.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqfveq.2: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( seq M ( .+ , G ) ` N ) )

  proof
    wph
    c.pl
    vk
    cF
    cG
    cM
    cM
    cN
    wph
    cM
    cz
    wcel
    #
    cM
    cM
    cuz
    cfv
    #
    wcel
    wph
    cN
    @1
    wcel
    #
    @0
    seqfveq.1
    cM
    cN
    eluzel2
    syl
    #
    cM
    uzid
    syl
    wph
    cM
    c.pl
    cF
    cM
    cseq
    cfv
    #
    cM
    cF
    cfv
    #
    cM
    cG
    cfv
    #
    wph
    @0
    @4
    @5
    wceq
    @3
    c.pl
    cF
    cM
    seq1
    syl
    wph
    cM
    cM
    cN
    cfz
    co
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    wceq
    #
    vk
    @7
    wral
    @5
    @6
    wceq
    #
    wph
    @2
    @8
    seqfveq.1
    cM
    cN
    eluzfz1
    syl
    wph
    @12
    vk
    @7
    seqfveq.2
    ralrimiva
    @12
    @13
    vk
    cM
    @7
    @9
    cM
    wceq
    @10
    @5
    @11
    @6
    @9
    cM
    cF
    fveq2
    @9
    cM
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    eqtrd
    seqfveq.1
    wph
    @9
    cM
    c1
    caddc
    co
    cN
    cfz
    co
    #
    wcel
    @9
    @7
    wcel
    @12
    wph
    @14
    @7
    @9
    wph
    @0
    @14
    @7
    wss
    @3
    cM
    cN
    fzp1ss
    syl
    sselda
    seqfveq.2
    syldan
    seqfveq2
end
