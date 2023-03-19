include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "nfcv.mm"
include "limsupre3uzlem.mm"
include "wb.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2d.mm"
include "cbvrex.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvralv.mm"
include "cbvrexv.mm"
include "breq2.mm"
include "raleqdv.mm"
include "breq1d.mm"
include "cbvral.mm"
include "anbi12i.mm"

theorem limsupre3uz
  let wph: wff ph
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vl: setvar l
  let vy: setvar y
  assume limsupre3uz.1: |- F/_ j F
  assume limsupre3uz.2: |- ( ph -> M e. ZZ )
  assume limsupre3uz.3: |- Z = ( ZZ>= ` M )
  assume limsupre3uz.4: |- ( ph -> F : Z --> RR* )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint F i
  disjoint F l
  disjoint F y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint k l
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint M i
  disjoint M l
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint i j
  disjoint j l
  disjoint j y
  disjoint i ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> ( ( limsup ` F ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) x <_ ( F ` j ) /\ E. x e. RR E. k e. Z A. j e. ( ZZ>= ` k ) ( F ` j ) <_ x ) ) )

  proof
    wph
    cF
    clsp
    cfv
    cr
    wcel
    vy
    cv
    #
    vl
    cv
    #
    cF
    cfv
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
    wrex
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    @2
    @0
    cle
    wbr
    #
    vl
    @5
    wral
    #
    vi
    cZ
    wrex
    #
    vy
    cr
    wrex
    #
    wa
    #
    vx
    cv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vj
    vk
    cv
    #
    cuz
    cfv
    #
    wrex
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @16
    @14
    cle
    wbr
    #
    vj
    @19
    wral
    #
    vk
    cZ
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
    vl
    vi
    cF
    cM
    cZ
    vl
    cF
    nfcv
    limsupre3uz.2
    limsupre3uz.3
    limsupre3uz.4
    limsupre3uzlem
    @13
    @27
    wb
    wph
    @8
    @22
    @12
    @26
    @7
    @21
    vy
    vx
    cr
    @0
    @14
    wceq
    #
    @7
    @14
    @2
    cle
    wbr
    #
    vl
    @5
    wrex
    #
    vi
    cZ
    wral
    #
    @21
    @28
    @6
    @30
    vi
    cZ
    @28
    @3
    @29
    vl
    @5
    @0
    @14
    @2
    cle
    breq1
    rexbidv
    ralbidv
    @31
    @21
    wb
    @28
    @30
    @20
    vi
    vk
    cZ
    @4
    @18
    wceq
    #
    @30
    @29
    vl
    @19
    wrex
    #
    @20
    @32
    @29
    vl
    @5
    @19
    @4
    @18
    cuz
    fveq2
    #
    rexeqdv
    @33
    @20
    wb
    @32
    @29
    @17
    vl
    vj
    @19
    vj
    @14
    @2
    cle
    vj
    @14
    nfcv
    #
    vj
    cle
    nfcv
    #
    vj
    @1
    cF
    limsupre3uz.1
    vj
    @1
    nfcv
    nffv
    #
    nfbr
    @17
    vl
    nfv
    @1
    @15
    wceq
    #
    @2
    @16
    @14
    cle
    @1
    @15
    cF
    fveq2
    #
    breq2d
    cbvrex
    a1i
    bitrd
    cbvralv
    a1i
    bitrd
    cbvrexv
    @11
    @25
    vy
    vx
    cr
    @28
    @11
    @2
    @14
    cle
    wbr
    #
    vl
    @5
    wral
    #
    vi
    cZ
    wrex
    #
    @25
    @28
    @10
    @41
    vi
    cZ
    @28
    @9
    @40
    vl
    @5
    @0
    @14
    @2
    cle
    breq2
    ralbidv
    rexbidv
    @42
    @25
    wb
    @28
    @41
    @24
    vi
    vk
    cZ
    @32
    @41
    @40
    vl
    @19
    wral
    #
    @24
    @32
    @40
    vl
    @5
    @19
    @34
    raleqdv
    @43
    @24
    wb
    @32
    @40
    @23
    vl
    vj
    @19
    vj
    @2
    @14
    cle
    @37
    @36
    @35
    nfbr
    @23
    vl
    nfv
    @38
    @2
    @16
    @14
    cle
    @39
    breq1d
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
