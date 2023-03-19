include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "fdmd.mm"
include "eqsstrd.mm"
include "ffdmd.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "nfdm.mm"
include "nfcv.mm"
include "rabeqf.mm"
include "syl.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "eqid.mm"
include "issmff.mm"

theorem issmfdf
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume issmfdf.x: |- F/_ x F
  assume issmfdf.a: |- F/ a ph
  assume issmfdf.s: |- ( ph -> S e. SAlg )
  assume issmfdf.d: |- ( ph -> D C_ U. S )
  assume issmfdf.f: |- ( ph -> F : D --> RR )
  assume issmfdf.p: |- ( ( ph /\ a e. RR ) -> { x e. D | ( F ` x ) < a } e. ( S |`t D ) )

  disjoint D x
  disjoint F a
  disjoint S a
  disjoint a x
  disjoint k x
  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    cF
    cdm
    #
    cS
    cuni
    #
    wss
    #
    @0
    cr
    cF
    wf
    #
    vx
    cv
    cF
    cfv
    va
    cv
    #
    clt
    wbr
    #
    vx
    @0
    crab
    #
    cS
    @0
    crest
    co
    #
    wcel
    #
    va
    cr
    wral
    #
    w3a
    wph
    @2
    @3
    @9
    wph
    @0
    cD
    @1
    wph
    cD
    cr
    cF
    issmfdf.f
    fdmd
    #
    issmfdf.d
    eqsstrd
    wph
    cD
    cr
    cF
    issmfdf.f
    ffdmd
    wph
    @8
    va
    cr
    issmfdf.a
    wph
    @4
    cr
    wcel
    #
    @8
    wph
    @11
    wa
    @8
    @5
    vx
    cD
    crab
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    issmfdf.p
    wph
    @8
    @14
    wb
    @11
    wph
    @6
    @12
    @7
    @13
    wph
    @0
    cD
    wceq
    @6
    @12
    wceq
    @10
    @5
    vx
    @0
    cD
    vx
    cF
    issmfdf.x
    nfdm
    vx
    cD
    nfcv
    rabeqf
    syl
    wph
    @0
    cD
    cS
    crest
    @10
    oveq2d
    eleq12d
    adantr
    mpbird
    ex
    ralrimi
    3jca
    wph
    vx
    @0
    cS
    cF
    va
    issmfdf.x
    issmfdf.s
    @0
    eqid
    issmff
    mpbird
end
