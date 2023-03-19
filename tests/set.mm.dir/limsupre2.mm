include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "nfcv.mm"
include "limsupre2lem.mm"
include "wb.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi1d.mm"
include "nfv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfan.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "cbvrex.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvralv.mm"
include "cbvrexv.mm"
include "imbi2d.mm"
include "imbi1d.mm"
include "nfim.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"

theorem limsupre2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsupre2.1: |- F/_ j F
  assume limsupre2.2: |- ( ph -> A C_ RR )
  assume limsupre2.3: |- ( ph -> F : A --> RR* )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint A i
  disjoint A l
  disjoint A y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j l
  disjoint j y
  disjoint k l
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint F i
  disjoint F l
  disjoint F y
  disjoint i ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x < ( F ` j ) ) /\ E. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) < x ) ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cr
    wcel
    vi
    cv
    #
    vl
    cv
    #
    cle
    wbr
    #
    vy
    cv
    #
    @1
    cF
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vl
    cA
    wrex
    #
    vi
    cr
    wral
    #
    vy
    cr
    wrex
    #
    @2
    @4
    @3
    clt
    wbr
    #
    wi
    #
    vl
    cA
    wral
    #
    vi
    cr
    wrex
    #
    vy
    cr
    wrex
    #
    wa
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @16
    cF
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vj
    cA
    wrex
    #
    vk
    cr
    wral
    #
    vx
    cr
    wrex
    #
    @17
    @19
    @18
    clt
    wbr
    #
    wi
    #
    vj
    cA
    wral
    #
    vk
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    wa
    wph
    vy
    cA
    vl
    vi
    cF
    vl
    cF
    nfcv
    limsupre2.2
    limsupre2.3
    limsupre2lem
    wph
    @9
    @24
    @14
    @29
    @9
    @24
    wb
    wph
    @8
    @23
    vy
    vx
    cr
    @3
    @18
    wceq
    #
    @8
    @2
    @18
    @4
    clt
    wbr
    #
    wa
    #
    vl
    cA
    wrex
    #
    vi
    cr
    wral
    #
    @23
    @30
    @7
    @33
    vi
    cr
    @30
    @6
    @32
    vl
    cA
    @30
    @5
    @31
    @2
    @3
    @18
    @4
    clt
    breq1
    anbi2d
    rexbidv
    ralbidv
    @34
    @23
    wb
    @30
    @33
    @22
    vi
    vk
    cr
    @0
    @15
    wceq
    #
    @33
    @15
    @1
    cle
    wbr
    #
    @31
    wa
    #
    vl
    cA
    wrex
    #
    @22
    @35
    @32
    @37
    vl
    cA
    @35
    @2
    @36
    @31
    @0
    @15
    @1
    cle
    breq1
    #
    anbi1d
    rexbidv
    @38
    @22
    wb
    @35
    @37
    @21
    vl
    vj
    cA
    @36
    @31
    vj
    @36
    vj
    nfv
    #
    vj
    @18
    @4
    clt
    vj
    @18
    nfcv
    #
    vj
    clt
    nfcv
    #
    vj
    @1
    cF
    limsupre2.1
    vj
    @1
    nfcv
    nffv
    #
    nfbr
    nfan
    @21
    vl
    nfv
    @1
    @16
    wceq
    #
    @36
    @17
    @31
    @20
    @1
    @16
    @15
    cle
    breq2
    #
    @44
    @4
    @19
    @18
    clt
    @1
    @16
    cF
    fveq2
    #
    breq2d
    anbi12d
    cbvrex
    a1i
    bitrd
    cbvralv
    a1i
    bitrd
    cbvrexv
    a1i
    @14
    @29
    wb
    wph
    @13
    @28
    vy
    vx
    cr
    @30
    @13
    @2
    @4
    @18
    clt
    wbr
    #
    wi
    #
    vl
    cA
    wral
    #
    vi
    cr
    wrex
    #
    @28
    @30
    @12
    @49
    vi
    cr
    @30
    @11
    @48
    vl
    cA
    @30
    @10
    @47
    @2
    @3
    @18
    @4
    clt
    breq2
    imbi2d
    ralbidv
    rexbidv
    @50
    @28
    wb
    @30
    @49
    @27
    vi
    vk
    cr
    @35
    @49
    @36
    @47
    wi
    #
    vl
    cA
    wral
    #
    @27
    @35
    @48
    @51
    vl
    cA
    @35
    @2
    @36
    @47
    @39
    imbi1d
    ralbidv
    @52
    @27
    wb
    @35
    @51
    @26
    vl
    vj
    cA
    @36
    @47
    vj
    @40
    vj
    @4
    @18
    clt
    @43
    @42
    @41
    nfbr
    nfim
    @26
    vl
    nfv
    @44
    @36
    @17
    @47
    @25
    @45
    @44
    @4
    @19
    @18
    clt
    @46
    breq1d
    imbi12d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvrexv
    a1i
    anbi12d
    bitrd
end
