include "clsxlim.mm"
include "wbr.mm"
include "cli.mm"
include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "wa.mm"
include "cpnf.mm"
include "w3o.mm"
include "dfxlim2v.mm"
include "biid.mm"
include "weq.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1d.mm"
include "cbvral.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "breq1.mm"
include "breq2d.mm"
include "3orbi123i.mm"

theorem dfxlim2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume dfxlim2.k: |- F/_ k F
  assume dfxlim2.m: |- ( ph -> M e. ZZ )
  assume dfxlim2.z: |- Z = ( ZZ>= ` M )
  assume dfxlim2.f: |- ( ph -> F : Z --> RR* )

  disjoint F j
  disjoint F x
  disjoint j x
  disjoint Z j
  disjoint Z x
  disjoint j k
  disjoint k x
  disjoint k x
  disjoint A i
  disjoint A l
  disjoint i l
  disjoint F i
  disjoint F l
  disjoint F y
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j l
  disjoint j y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint i k
  disjoint k l
  disjoint k y
  disjoint i ph
  disjoint l ph
  assert |- ( ph -> ( F ~~>* A <-> ( F ~~> A \/ ( A = -oo /\ A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) <_ x ) \/ ( A = +oo /\ A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) x <_ ( F ` k ) ) ) ) )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    cF
    cA
    cli
    wbr
    #
    cA
    cmnf
    wceq
    #
    vl
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cle
    wbr
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
    cZ
    wrex
    #
    vy
    cr
    wral
    #
    wa
    #
    cA
    cpnf
    wceq
    #
    @4
    @3
    cle
    wbr
    #
    vl
    @7
    wral
    vi
    cZ
    wrex
    #
    vy
    cr
    wral
    #
    wa
    #
    w3o
    @0
    @1
    vk
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cle
    wbr
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
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    wa
    #
    @11
    @18
    @17
    cle
    wbr
    #
    vk
    @21
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    wa
    #
    w3o
    wph
    vy
    cA
    vi
    vl
    cF
    cM
    cZ
    dfxlim2.m
    dfxlim2.z
    dfxlim2.f
    dfxlim2v
    @0
    @0
    @10
    @25
    @15
    @30
    @0
    biid
    @9
    @24
    @1
    @8
    @23
    vy
    vx
    cr
    vy
    vx
    weq
    #
    @8
    @3
    @18
    cle
    wbr
    #
    vl
    @7
    wral
    #
    vi
    cZ
    wrex
    @23
    @31
    @5
    @32
    vi
    vl
    cZ
    @7
    @4
    @18
    @3
    cle
    breq2
    rexralbidv
    @33
    @22
    vi
    vj
    cZ
    vi
    vj
    weq
    #
    @33
    @32
    vl
    @21
    wral
    @22
    @34
    @32
    vl
    @7
    @21
    @6
    @20
    cuz
    fveq2
    #
    raleqdv
    @32
    @19
    vl
    vk
    @21
    vk
    @3
    @18
    cle
    vk
    @2
    cF
    dfxlim2.k
    vk
    @2
    nfcv
    nffv
    #
    vk
    cle
    nfcv
    #
    vk
    @18
    nfcv
    #
    nfbr
    @19
    vl
    nfv
    vl
    vk
    weq
    #
    @3
    @17
    @18
    cle
    @2
    @16
    cF
    fveq2
    #
    breq1d
    cbvral
    syl6bb
    cbvrexv
    syl6bb
    cbvralv
    anbi2i
    @14
    @29
    @11
    @13
    @28
    vy
    vx
    cr
    @31
    @13
    @18
    @3
    cle
    wbr
    #
    vl
    @7
    wral
    #
    vi
    cZ
    wrex
    @28
    @31
    @12
    @41
    vi
    vl
    cZ
    @7
    @4
    @18
    @3
    cle
    breq1
    rexralbidv
    @42
    @27
    vi
    vj
    cZ
    @34
    @42
    @41
    vl
    @21
    wral
    @27
    @34
    @41
    vl
    @7
    @21
    @35
    raleqdv
    @41
    @26
    vl
    vk
    @21
    vk
    @18
    @3
    cle
    @38
    @37
    @36
    nfbr
    @26
    vl
    nfv
    @39
    @3
    @17
    @18
    cle
    @40
    breq2d
    cbvral
    syl6bb
    cbvrexv
    syl6bb
    cbvralv
    anbi2i
    3orbi123i
    syl6bb
end
