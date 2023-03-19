include "clsp.mm"
include "cfv.mm"
include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "eqid.mm"
include "limsupmnflem.mm"
include "wb.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "breq1.mm"
include "imbi1d.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "cbvralv.mm"

theorem limsupmnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsupmnf.j: |- F/_ j F
  assume limsupmnf.a: |- ( ph -> A C_ RR )
  assume limsupmnf.f: |- ( ph -> F : A --> RR* )

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
  assert |- ( ph -> ( ( limsup ` F ) = -oo <-> A. x e. RR E. k e. RR A. j e. A ( k <_ j -> ( F ` j ) <_ x ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cmnf
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
    @1
    cF
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
    @11
    cF
    cfv
    #
    vx
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
    vi
    cr
    cF
    @0
    cpnf
    cico
    co
    cima
    cxr
    clt
    csup
    cmpt
    #
    limsupmnf.a
    limsupmnf.f
    @20
    eqid
    limsupmnflem
    @9
    @19
    wb
    wph
    @8
    @18
    vy
    vx
    cr
    @4
    @14
    wceq
    #
    @8
    @2
    @3
    @14
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
    @18
    @21
    @7
    @24
    vi
    cr
    @21
    @6
    @23
    vl
    cA
    @21
    @5
    @22
    @2
    @4
    @14
    @3
    cle
    breq2
    imbi2d
    ralbidv
    rexbidv
    @25
    @18
    wb
    @21
    @24
    @17
    vi
    vk
    cr
    @0
    @10
    wceq
    #
    @24
    @10
    @1
    cle
    wbr
    #
    @22
    wi
    #
    vl
    cA
    wral
    #
    @17
    @26
    @23
    @28
    vl
    cA
    @26
    @2
    @27
    @22
    @0
    @10
    @1
    cle
    breq1
    imbi1d
    ralbidv
    @29
    @17
    wb
    @26
    @28
    @16
    vl
    vj
    cA
    @27
    @22
    vj
    @27
    vj
    nfv
    vj
    @3
    @14
    cle
    vj
    @1
    cF
    limsupmnf.j
    vj
    @1
    nfcv
    nffv
    vj
    cle
    nfcv
    vj
    @14
    nfcv
    nfbr
    nfim
    @16
    vl
    nfv
    @1
    @11
    wceq
    #
    @27
    @12
    @22
    @15
    @1
    @11
    @10
    cle
    breq2
    @30
    @3
    @13
    @14
    cle
    @1
    @11
    cF
    fveq2
    breq1d
    imbi12d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvralv
    a1i
    bitrd
end
