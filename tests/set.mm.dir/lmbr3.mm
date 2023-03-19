include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "lmbr3v.mm"
include "weq.mm"
include "eleq2w.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "nfcv.mm"
include "nfdm.mm"
include "nfel.mm"
include "nffv.mm"
include "nfan.mm"
include "nfv.mm"
include "eleq1w.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cbvral.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "3anbi3i.mm"

theorem lmbr3
  let wph: wff ph
  let vu: setvar u
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vi: setvar i
  let vl: setvar l
  let vv: setvar v
  assume lmbr3.1: |- F/_ k F
  assume lmbr3.2: |- ( ph -> J e. ( TopOn ` X ) )

  disjoint F j
  disjoint F u
  disjoint j u
  disjoint J u
  disjoint P u
  disjoint j k
  disjoint k u
  disjoint F i
  disjoint F l
  disjoint F v
  disjoint i j
  disjoint i l
  disjoint i u
  disjoint i v
  disjoint j l
  disjoint j v
  disjoint l u
  disjoint l v
  disjoint u v
  disjoint J i
  disjoint J l
  disjoint J v
  disjoint P i
  disjoint P l
  disjoint P v
  disjoint X i
  disjoint X l
  disjoint X v
  disjoint i k
  disjoint k l
  disjoint k v
  disjoint i ph
  disjoint l ph
  disjoint ph v
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. u e. J ( P e. u -> E. j e. ZZ A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. u ) ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vv
    cv
    #
    wcel
    #
    vl
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @4
    cF
    cfv
    #
    @2
    wcel
    #
    wa
    #
    vl
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    vi
    cz
    wrex
    #
    wi
    #
    vv
    cJ
    wral
    #
    w3a
    @0
    @1
    cP
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    @5
    wcel
    #
    @17
    cF
    cfv
    #
    @15
    wcel
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cz
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    wph
    vv
    cP
    vi
    vl
    cF
    cJ
    cX
    lmbr3.2
    lmbr3v
    @14
    @27
    @0
    @1
    @13
    @26
    vv
    vu
    cJ
    vv
    vu
    weq
    #
    @3
    @16
    @12
    @25
    vv
    vu
    cP
    eleq2w
    @28
    @12
    @6
    @7
    @15
    wcel
    #
    wa
    #
    vl
    @11
    wral
    #
    vi
    cz
    wrex
    @25
    @28
    @9
    @30
    vi
    vl
    cz
    @11
    @28
    @8
    @29
    @6
    vv
    vu
    @7
    eleq2w
    anbi2d
    rexralbidv
    @31
    @24
    vi
    vj
    cz
    vi
    vj
    weq
    #
    @31
    @30
    vl
    @23
    wral
    @24
    @32
    @30
    vl
    @11
    @23
    @10
    @22
    cuz
    fveq2
    raleqdv
    @30
    @21
    vl
    vk
    @23
    @6
    @29
    vk
    vk
    @4
    @5
    vk
    @4
    nfcv
    #
    vk
    cF
    lmbr3.1
    nfdm
    nfel
    vk
    @7
    @15
    vk
    @4
    cF
    lmbr3.1
    @33
    nffv
    vk
    @15
    nfcv
    nfel
    nfan
    @21
    vl
    nfv
    vl
    vk
    weq
    #
    @6
    @18
    @29
    @20
    vl
    vk
    @5
    eleq1w
    @34
    @7
    @19
    @15
    @4
    @17
    cF
    fveq2
    eleq1d
    anbi12d
    cbvral
    syl6bb
    cbvrexv
    syl6bb
    imbi12d
    cbvralv
    3anbi3i
    syl6bb
end
