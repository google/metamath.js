include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
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
include "issmf.mm"
include "wb.mm"
include "nfcv.mm"
include "cdm.mm"
include "nfdm.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrab.mm"
include "eleq1i.mm"
include "ralbii.mm"
include "3anbi3i.mm"
include "a1i.mm"
include "bitrd.mm"

theorem issmff
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vy: setvar y
  let vk: setvar k
  assume issmff.x: |- F/_ x F
  assume issmff.s: |- ( ph -> S e. SAlg )
  assume issmff.d: |- D = dom F

  disjoint D a
  disjoint F a
  disjoint S a
  disjoint a x
  disjoint D y
  disjoint a y
  disjoint F y
  disjoint x y
  disjoint k x
  assert |- ( ph -> ( F e. ( SMblFn ` S ) <-> ( D C_ U. S /\ F : D --> RR /\ A. a e. RR { x e. D | ( F ` x ) < a } e. ( S |`t D ) ) ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    cD
    cS
    cuni
    wss
    #
    cD
    cr
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    va
    cv
    #
    clt
    wbr
    #
    vy
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
    va
    cr
    wral
    #
    w3a
    #
    @0
    @1
    vx
    cv
    #
    cF
    cfv
    #
    @4
    clt
    wbr
    #
    vx
    cD
    crab
    #
    @7
    wcel
    #
    va
    cr
    wral
    #
    w3a
    #
    wph
    vy
    cD
    cS
    cF
    va
    issmff.s
    issmff.d
    issmf
    @10
    @17
    wb
    wph
    @9
    @16
    @0
    @1
    @8
    @15
    va
    cr
    @6
    @14
    @7
    @5
    @13
    vy
    vx
    cD
    vy
    cD
    nfcv
    vx
    cD
    cF
    cdm
    issmff.d
    vx
    cF
    issmff.x
    nfdm
    nfcxfr
    vx
    @3
    @4
    clt
    vx
    @2
    cF
    issmff.x
    vx
    @2
    nfcv
    nffv
    vx
    clt
    nfcv
    vx
    @4
    nfcv
    nfbr
    @13
    vy
    nfv
    @2
    @11
    wceq
    @3
    @12
    @4
    clt
    @2
    @11
    cF
    fveq2
    breq1d
    cbvrab
    eleq1i
    ralbii
    3anbi3i
    a1i
    bitrd
end
