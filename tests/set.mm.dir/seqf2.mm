include "cuz.mm"
include "cfv.mm"
include "cseq.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cz.mm"
include "seqfn.mm"
include "syl.mm"
include "wa.mm"
include "adantr.mm"
include "co.mm"
include "adantlr.mm"
include "simpr.mm"
include "c1.mm"
include "caddc.mm"
include "cfz.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "seqcl2.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "feq2i.mm"
include "sylibr.mm"

theorem seqf2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  assume seqcl2.1: |- ( ph -> ( F ` M ) e. C )
  assume seqcl2.2: |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x .+ y ) e. C )
  assume seqf2.3: |- Z = ( ZZ>= ` M )
  assume seqf2.4: |- ( ph -> M e. ZZ )
  assume seqf2.5: |- ( ( ph /\ x e. ( ZZ>= ` ( M + 1 ) ) ) -> ( F ` x ) e. D )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint .+ x
  disjoint .+ y
  disjoint ph x
  disjoint ph y
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint C k
  disjoint n x
  disjoint n y
  disjoint C n
  disjoint F k
  disjoint F n
  disjoint M k
  disjoint M n
  disjoint N n
  disjoint N x
  disjoint .+ k
  disjoint .+ n
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> seq M ( .+ , F ) : Z --> C )

  proof
    wph
    cM
    cuz
    cfv
    #
    cC
    c.pl
    cF
    cM
    cseq
    #
    wf
    #
    cZ
    cC
    @1
    wf
    wph
    @1
    @0
    wfn
    #
    vk
    cv
    #
    @1
    cfv
    cC
    wcel
    #
    vk
    @0
    wral
    @2
    wph
    cM
    cz
    wcel
    @3
    seqf2.4
    c.pl
    cF
    cM
    seqfn
    syl
    wph
    @5
    vk
    @0
    wph
    @4
    @0
    wcel
    #
    wa
    vx
    vy
    cC
    cD
    c.pl
    cF
    cM
    @4
    wph
    cM
    cF
    cfv
    cC
    wcel
    @6
    seqcl2.1
    adantr
    wph
    vx
    cv
    #
    cC
    wcel
    vy
    cv
    #
    cD
    wcel
    wa
    @7
    @8
    c.pl
    co
    cC
    wcel
    @6
    seqcl2.2
    adantlr
    wph
    @6
    simpr
    wph
    @7
    cM
    c1
    caddc
    co
    #
    @4
    cfz
    co
    wcel
    #
    @7
    cF
    cfv
    cD
    wcel
    #
    @6
    @10
    wph
    @7
    @9
    cuz
    cfv
    wcel
    @11
    @7
    @9
    @4
    elfzuz
    seqf2.5
    sylan2
    adantlr
    seqcl2
    ralrimiva
    vk
    @0
    cC
    @1
    ffnfv
    sylanbrc
    cZ
    @0
    cC
    @1
    seqf2.3
    feq2i
    sylibr
end
