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
include "wceq.mm"
include "rabeqd.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "eqid.mm"
include "issmfgt.mm"

theorem issmfgtd
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume issmfgtd.a: |- F/ a ph
  assume issmfgtd.s: |- ( ph -> S e. SAlg )
  assume issmfgtd.d: |- ( ph -> D C_ U. S )
  assume issmfgtd.f: |- ( ph -> F : D --> RR )
  assume issmfgtd.p: |- ( ( ph /\ a e. RR ) -> { x e. D | a < ( F ` x ) } e. ( S |`t D ) )

  disjoint D x
  disjoint F a
  disjoint F x
  disjoint a x
  disjoint S a
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
    va
    cv
    #
    vx
    cv
    cF
    cfv
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
    issmfgtd.f
    fdmd
    #
    issmfgtd.d
    eqsstrd
    wph
    cD
    cr
    cF
    issmfgtd.f
    ffdmd
    wph
    @8
    va
    cr
    issmfgtd.a
    wph
    @4
    cr
    wcel
    #
    @8
    wph
    @11
    wa
    #
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
    issmfgtd.p
    @12
    @6
    @13
    @7
    @14
    wph
    @6
    @13
    wceq
    @11
    wph
    @5
    vx
    @0
    cD
    @10
    rabeqd
    adantr
    wph
    @7
    @14
    wceq
    @11
    wph
    @0
    cD
    cS
    crest
    @10
    oveq2d
    adantr
    eleq12d
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
    issmfgtd.s
    @0
    eqid
    issmfgt
    mpbird
end
