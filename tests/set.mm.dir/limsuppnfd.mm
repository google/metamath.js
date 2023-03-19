include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "wb.mm"
include "anbi1d.mm"
include "nfv.mm"
include "nfcv.mm"
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
include "sylib.mm"
include "eqid.mm"
include "limsuppnfdlem.mm"

theorem limsuppnfd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsuppnfd.j: |- F/_ j F
  assume limsuppnfd.a: |- ( ph -> A C_ RR )
  assume limsuppnfd.f: |- ( ph -> F : A --> RR* )
  assume limsuppnfd.u: |- ( ph -> A. x e. RR A. k e. RR E. j e. A ( k <_ j /\ x <_ ( F ` j ) ) )

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
  assert |- ( ph -> ( limsup ` F ) = +oo )

  proof
    wph
    vy
    cA
    vl
    vi
    cF
    vi
    cr
    cF
    vi
    cv
    #
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    cmpt
    #
    limsuppnfd.a
    limsuppnfd.f
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
    vx
    cv
    #
    @3
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
    @0
    vl
    cv
    #
    cle
    wbr
    #
    vy
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
    limsuppnfd.u
    @10
    @18
    vx
    vy
    cr
    @5
    @13
    wceq
    #
    @10
    @4
    @13
    @6
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
    @19
    @9
    @22
    vk
    cr
    @19
    @8
    @21
    vj
    cA
    @19
    @7
    @20
    @4
    @5
    @13
    @6
    cle
    breq1
    anbi2d
    rexbidv
    ralbidv
    @23
    @18
    wb
    @19
    @22
    @17
    vk
    vi
    cr
    @2
    @0
    wceq
    #
    @22
    @0
    @3
    cle
    wbr
    #
    @20
    wa
    #
    vj
    cA
    wrex
    #
    @17
    @24
    @21
    @26
    vj
    cA
    @24
    @4
    @25
    @20
    @2
    @0
    @3
    cle
    breq1
    anbi1d
    rexbidv
    @27
    @17
    wb
    @24
    @26
    @16
    vj
    vl
    cA
    @26
    vl
    nfv
    @12
    @15
    vj
    @12
    vj
    nfv
    vj
    @13
    @14
    cle
    vj
    @13
    nfcv
    vj
    cle
    nfcv
    vj
    @11
    cF
    limsuppnfd.j
    vj
    @11
    nfcv
    nffv
    nfbr
    nfan
    @3
    @11
    wceq
    #
    @25
    @12
    @20
    @15
    @3
    @11
    @0
    cle
    breq2
    @28
    @6
    @14
    @13
    cle
    @3
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
    bitrd
    cbvralv
    sylib
    @1
    eqid
    limsuppnfdlem
end
