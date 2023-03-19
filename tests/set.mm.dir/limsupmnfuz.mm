include "clsp.mm"
include "cfv.mm"
include "cmnf.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "limsupmnfuzlem.mm"
include "wb.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "cbvralv.mm"

theorem limsupmnfuz
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
  assume limsupmnfuz.1: |- F/_ j F
  assume limsupmnfuz.2: |- ( ph -> M e. ZZ )
  assume limsupmnfuz.3: |- Z = ( ZZ>= ` M )
  assume limsupmnfuz.4: |- ( ph -> F : Z --> RR* )

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
  assert |- ( ph -> ( ( limsup ` F ) = -oo <-> A. x e. RR E. k e. Z A. j e. ( ZZ>= ` k ) ( F ` j ) <_ x ) )

  proof
    wph
    cF
    clsp
    cfv
    cmnf
    wceq
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
    #
    vi
    cZ
    wrex
    #
    vy
    cr
    wral
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
    wral
    #
    vk
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    wph
    vy
    vl
    vi
    cF
    cM
    cZ
    limsupmnfuz.2
    limsupmnfuz.3
    limsupmnfuz.4
    limsupmnfuzlem
    @8
    @17
    wb
    wph
    @7
    @16
    vy
    vx
    cr
    @2
    @11
    wceq
    #
    @7
    @1
    @11
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
    @16
    @18
    @6
    @20
    vi
    cZ
    @18
    @3
    @19
    vl
    @5
    @2
    @11
    @1
    cle
    breq2
    ralbidv
    rexbidv
    @21
    @16
    wb
    @18
    @20
    @15
    vi
    vk
    cZ
    @4
    @13
    wceq
    #
    @20
    @19
    vl
    @14
    wral
    #
    @15
    @22
    @19
    vl
    @5
    @14
    @4
    @13
    cuz
    fveq2
    raleqdv
    @23
    @15
    wb
    @22
    @19
    @12
    vl
    vj
    @14
    vj
    @1
    @11
    cle
    vj
    @0
    cF
    limsupmnfuz.1
    vj
    @0
    nfcv
    nffv
    vj
    cle
    nfcv
    vj
    @11
    nfcv
    nfbr
    @12
    vl
    nfv
    @0
    @9
    wceq
    @1
    @10
    @11
    cle
    @0
    @9
    cF
    fveq2
    breq1d
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
