include "clsp.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "nfcv.mm"
include "limsuppnflem.mm"
include "wb.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
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
include "anbi2d.mm"
include "ralbidv.mm"

theorem limsuppnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsuppnf.j: |- F/_ j F
  assume limsuppnf.a: |- ( ph -> A C_ RR )
  assume limsuppnf.f: |- ( ph -> F : A --> RR* )

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
  assert |- ( ph -> ( ( limsup ` F ) = +oo <-> A. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cpnf
    wceq
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
    wral
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
    @11
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
    wral
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
    limsuppnf.a
    limsuppnf.f
    limsuppnflem
    @9
    @19
    wb
    wph
    @8
    @18
    vy
    vx
    cr
    @3
    @13
    wceq
    #
    @8
    @12
    @3
    @14
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
    @18
    @8
    @24
    wb
    @20
    @7
    @23
    vi
    vk
    cr
    @0
    @10
    wceq
    #
    @7
    @10
    @1
    cle
    wbr
    #
    @5
    wa
    #
    vl
    cA
    wrex
    #
    @23
    @25
    @6
    @27
    vl
    cA
    @25
    @2
    @26
    @5
    @0
    @10
    @1
    cle
    breq1
    anbi1d
    rexbidv
    @28
    @23
    wb
    @25
    @27
    @22
    vl
    vj
    cA
    @26
    @5
    vj
    @26
    vj
    nfv
    vj
    @3
    @4
    cle
    vj
    @3
    nfcv
    vj
    cle
    nfcv
    vj
    @1
    cF
    limsuppnf.j
    vj
    @1
    nfcv
    nffv
    nfbr
    nfan
    @22
    vl
    nfv
    @1
    @11
    wceq
    #
    @26
    @12
    @5
    @21
    @1
    @11
    @10
    cle
    breq2
    @29
    @4
    @14
    @3
    cle
    @1
    @11
    cF
    fveq2
    breq2d
    anbi12d
    cbvrex
    a1i
    bitrd
    cbvralv
    a1i
    @20
    @23
    @17
    vk
    cr
    @20
    @22
    @16
    vj
    cA
    @20
    @21
    @15
    @12
    @3
    @13
    @14
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    bitrd
    cbvralv
    a1i
    bitrd
end
