include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "nfcv.mm"
include "limsupre3lem.mm"
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
include "anbi12i.mm"

theorem limsupre3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsupre3.1: |- F/_ j F
  assume limsupre3.2: |- ( ph -> A C_ RR )
  assume limsupre3.3: |- ( ph -> F : A --> RR* )

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
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) /\ E. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) <_ x ) ) ) )

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
    cle
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
    cle
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
    #
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
    @17
    cF
    cfv
    #
    cle
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
    @18
    @20
    @19
    cle
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
    #
    wph
    vy
    cA
    vl
    vi
    cF
    vl
    cF
    nfcv
    limsupre3.2
    limsupre3.3
    limsupre3lem
    @15
    @31
    wb
    wph
    @9
    @25
    @14
    @30
    @8
    @24
    vy
    vx
    cr
    @3
    @19
    wceq
    #
    @8
    @2
    @19
    @4
    cle
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
    @24
    @32
    @7
    @35
    vi
    cr
    @32
    @6
    @34
    vl
    cA
    @32
    @5
    @33
    @2
    @3
    @19
    @4
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    @36
    @24
    wb
    @32
    @35
    @23
    vi
    vk
    cr
    @0
    @16
    wceq
    #
    @35
    @16
    @1
    cle
    wbr
    #
    @33
    wa
    #
    vl
    cA
    wrex
    #
    @23
    @37
    @34
    @39
    vl
    cA
    @37
    @2
    @38
    @33
    @0
    @16
    @1
    cle
    breq1
    #
    anbi1d
    rexbidv
    @40
    @23
    wb
    @37
    @39
    @22
    vl
    vj
    cA
    @38
    @33
    vj
    @38
    vj
    nfv
    #
    vj
    @19
    @4
    cle
    vj
    @19
    nfcv
    #
    vj
    cle
    nfcv
    #
    vj
    @1
    cF
    limsupre3.1
    vj
    @1
    nfcv
    nffv
    #
    nfbr
    nfan
    @22
    vl
    nfv
    @1
    @17
    wceq
    #
    @38
    @18
    @33
    @21
    @1
    @17
    @16
    cle
    breq2
    #
    @46
    @4
    @20
    @19
    cle
    @1
    @17
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
    @13
    @29
    vy
    vx
    cr
    @32
    @13
    @2
    @4
    @19
    cle
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
    @29
    @32
    @12
    @51
    vi
    cr
    @32
    @11
    @50
    vl
    cA
    @32
    @10
    @49
    @2
    @3
    @19
    @4
    cle
    breq2
    imbi2d
    ralbidv
    rexbidv
    @52
    @29
    wb
    @32
    @51
    @28
    vi
    vk
    cr
    @37
    @51
    @38
    @49
    wi
    #
    vl
    cA
    wral
    #
    @28
    @37
    @50
    @53
    vl
    cA
    @37
    @2
    @38
    @49
    @41
    imbi1d
    ralbidv
    @54
    @28
    wb
    @37
    @53
    @27
    vl
    vj
    cA
    @38
    @49
    vj
    @42
    vj
    @4
    @19
    cle
    @45
    @44
    @43
    nfbr
    nfim
    @27
    vl
    nfv
    @46
    @38
    @18
    @49
    @26
    @47
    @46
    @4
    @20
    @19
    cle
    @48
    breq1d
    imbi12d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvrexv
    anbi12i
    a1i
    bitrd
end
