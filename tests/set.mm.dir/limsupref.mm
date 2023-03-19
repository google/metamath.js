include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "wb.mm"
include "breq1.mm"
include "imbi1d.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "limsupre.mm"

theorem limsupref
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vb: setvar b
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  assume limsupref.j: |- F/_ j F
  assume limsupref.a: |- ( ph -> A C_ RR )
  assume limsupref.s: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume limsupref.f: |- ( ph -> F : A --> RR )
  assume limsupref.b: |- ( ph -> E. b e. RR E. k e. RR A. j e. A ( k <_ j -> ( abs ` ( F ` j ) ) <_ b ) )

  disjoint A b
  disjoint A j
  disjoint A k
  disjoint b j
  disjoint b k
  disjoint j k
  disjoint F b
  disjoint F k
  disjoint A i
  disjoint A x
  disjoint A y
  disjoint b i
  disjoint b x
  disjoint b y
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint F i
  disjoint F x
  disjoint F y
  disjoint i ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( limsup ` F ) e. RR )

  proof
    wph
    cA
    vx
    vi
    cF
    vy
    limsupref.a
    limsupref.s
    limsupref.f
    wph
    vk
    cv
    #
    vj
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    #
    cabs
    cfv
    #
    vb
    cv
    #
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
    vb
    cr
    wrex
    vi
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    @11
    cF
    cfv
    #
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    wi
    #
    vx
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
    limsupref.b
    @9
    @19
    vb
    vy
    cr
    @5
    @15
    wceq
    #
    @9
    @2
    @4
    @15
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
    @19
    @20
    @8
    @23
    vk
    cr
    @20
    @7
    @22
    vj
    cA
    @20
    @6
    @21
    @2
    @5
    @15
    @4
    cle
    breq2
    imbi2d
    ralbidv
    rexbidv
    @24
    @19
    wb
    @20
    @23
    @18
    vk
    vi
    cr
    @0
    @10
    wceq
    #
    @23
    @10
    @1
    cle
    wbr
    #
    @21
    wi
    #
    vj
    cA
    wral
    #
    @18
    @25
    @22
    @27
    vj
    cA
    @25
    @2
    @26
    @21
    @0
    @10
    @1
    cle
    breq1
    imbi1d
    ralbidv
    @28
    @18
    wb
    @25
    @27
    @17
    vj
    vx
    cA
    @27
    vx
    nfv
    @12
    @16
    vj
    @12
    vj
    nfv
    vj
    @14
    @15
    cle
    vj
    @13
    cabs
    vj
    cabs
    nfcv
    vj
    @11
    cF
    limsupref.j
    vj
    @11
    nfcv
    nffv
    nffv
    vj
    cle
    nfcv
    vj
    @15
    nfcv
    nfbr
    nfim
    @1
    @11
    wceq
    #
    @26
    @12
    @21
    @16
    @1
    @11
    @10
    cle
    breq2
    @29
    @4
    @14
    @15
    cle
    @29
    @3
    @13
    cabs
    @1
    @11
    cF
    fveq2
    fveq2d
    breq1d
    imbi12d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvrexv
    sylib
    limsupre
end
