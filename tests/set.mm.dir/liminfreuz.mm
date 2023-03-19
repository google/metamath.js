include "clsi.mm"
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
include "liminfreuzlem.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "fveq2.mm"
include "rexeqdv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1d.mm"
include "cbvrex.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvralv.mm"
include "cbvrexv.mm"
include "breq1.mm"
include "breq2d.mm"
include "cbvral.mm"
include "anbi12i.mm"

theorem liminfreuz
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
  assume liminfreuz.1: |- F/_ j F
  assume liminfreuz.2: |- ( ph -> M e. ZZ )
  assume liminfreuz.3: |- Z = ( ZZ>= ` M )
  assume liminfreuz.4: |- ( ph -> F : Z --> RR )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint k x
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
  assert |- ( ph -> ( ( liminf ` F ) e. RR <-> ( E. x e. RR A. k e. Z E. j e. ( ZZ>= ` k ) ( F ` j ) <_ x /\ E. x e. RR A. j e. Z x <_ ( F ` j ) ) ) )

  proof
    wph
    cF
    clsi
    cfv
    cr
    wcel
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
    @1
    cle
    wbr
    #
    vl
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    wa
    #
    vj
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
    @15
    @14
    cle
    wbr
    #
    vj
    cZ
    wral
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
    liminfreuz.2
    liminfreuz.3
    liminfreuz.4
    liminfreuzlem
    @12
    @25
    wb
    wph
    @8
    @21
    @11
    @24
    @7
    @20
    vy
    vx
    cr
    @2
    @15
    wceq
    #
    @7
    @1
    @15
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
    @20
    @26
    @6
    @28
    vi
    cZ
    @26
    @3
    @27
    vl
    @5
    @2
    @15
    @1
    cle
    breq2
    rexbidv
    ralbidv
    @29
    @20
    wb
    @26
    @28
    @19
    vi
    vk
    cZ
    @4
    @17
    wceq
    #
    @28
    @27
    vl
    @18
    wrex
    #
    @19
    @30
    @27
    vl
    @5
    @18
    @4
    @17
    cuz
    fveq2
    rexeqdv
    @31
    @19
    wb
    @30
    @27
    @16
    vl
    vj
    @18
    vj
    @1
    @15
    cle
    vj
    @0
    cF
    liminfreuz.1
    vj
    @0
    nfcv
    nffv
    #
    vj
    cle
    nfcv
    #
    vj
    @15
    nfcv
    #
    nfbr
    @16
    vl
    nfv
    @0
    @13
    wceq
    #
    @1
    @14
    @15
    cle
    @0
    @13
    cF
    fveq2
    #
    breq1d
    cbvrex
    a1i
    bitrd
    cbvralv
    a1i
    bitrd
    cbvrexv
    @10
    @23
    vy
    vx
    cr
    @26
    @10
    @15
    @1
    cle
    wbr
    #
    vl
    cZ
    wral
    #
    @23
    @26
    @9
    @37
    vl
    cZ
    @2
    @15
    @1
    cle
    breq1
    ralbidv
    @38
    @23
    wb
    @26
    @37
    @22
    vl
    vj
    cZ
    vj
    @15
    @1
    cle
    @34
    @33
    @32
    nfbr
    @22
    vl
    nfv
    @35
    @1
    @14
    @15
    cle
    @36
    breq2d
    cbvral
    a1i
    bitrd
    cbvrexv
    anbi12i
    a1i
    bitrd
end
