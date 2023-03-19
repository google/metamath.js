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
include "issmflem.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "eleq1i.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvralv.mm"
include "3anbi3i.mm"

theorem issmf
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume issmf.s: |- ( ph -> S e. SAlg )
  assume issmf.d: |- D = dom F

  disjoint D a
  disjoint D x
  disjoint a x
  disjoint F a
  disjoint F x
  disjoint S a
  disjoint D b
  disjoint D y
  disjoint a b
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint F b
  disjoint F y
  disjoint S b
  disjoint S y
  disjoint b ph
  disjoint ph y
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
    vb
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
    vb
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
    va
    cv
    #
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
    vb
    issmf.s
    issmf.d
    issmflem
    @10
    @18
    wb
    wph
    @9
    @17
    @0
    @1
    @8
    @16
    vb
    va
    cr
    @4
    @13
    wceq
    #
    @8
    @3
    @13
    clt
    wbr
    #
    vy
    cD
    crab
    #
    @7
    wcel
    #
    @16
    @19
    @6
    @21
    @7
    @19
    @5
    @20
    vy
    cD
    @4
    @13
    @3
    clt
    breq2
    rabbidv
    eleq1d
    @22
    @16
    wb
    @19
    @21
    @15
    @7
    @20
    @14
    vy
    vx
    cD
    @2
    @11
    wceq
    @3
    @12
    @13
    clt
    @2
    @11
    cF
    fveq2
    breq1d
    cbvrabv
    eleq1i
    a1i
    bitrd
    cbvralv
    3anbi3i
    a1i
    bitrd
end
