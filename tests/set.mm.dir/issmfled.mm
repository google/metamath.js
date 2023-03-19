include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
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
include "rabeqd.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "eqid.mm"
include "issmfle.mm"

theorem issmfled
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vk: setvar k
  assume issmfled.a: |- F/ a ph
  assume issmfled.s: |- ( ph -> S e. SAlg )
  assume issmfled.d: |- ( ph -> D C_ U. S )
  assume issmfled.f: |- ( ph -> F : D --> RR )
  assume issmfled.6: |- ( ( ph /\ a e. RR ) -> { x e. D | ( F ` x ) <_ a } e. ( S |`t D ) )

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
    vx
    cv
    cF
    cfv
    va
    cv
    #
    cle
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
    issmfled.f
    fdmd
    #
    issmfled.d
    eqsstrd
    wph
    cD
    cr
    cF
    issmfled.f
    ffdmd
    wph
    @8
    va
    cr
    issmfled.a
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
    issmfled.6
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
    @5
    vx
    @0
    cD
    @10
    rabeqd
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
    issmfled.s
    @0
    eqid
    issmfle
    mpbird
end
