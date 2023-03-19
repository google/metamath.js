include "cmnf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "xlimmnfv.mm"
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

theorem xlimmnf
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
  assume xlimmnf.k: |- F/_ k F
  assume xlimmnf.m: |- ( ph -> M e. ZZ )
  assume xlimmnf.z: |- Z = ( ZZ>= ` M )
  assume xlimmnf.f: |- ( ph -> F : Z --> RR* )

  disjoint F j
  disjoint F x
  disjoint j x
  disjoint Z j
  disjoint Z x
  disjoint j k
  disjoint k x
  disjoint k x
  disjoint F i
  disjoint F l
  disjoint F y
  disjoint i j
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j l
  disjoint j y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint M i
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint i k
  disjoint k l
  disjoint k y
  disjoint i ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> ( F ~~>* -oo <-> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) ( F ` k ) <_ x ) )

  proof
    wph
    cF
    cmnf
    clsxlim
    wbr
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
    wph
    vy
    vi
    vl
    cF
    cM
    cZ
    xlimmnf.m
    xlimmnf.z
    xlimmnf.f
    xlimmnfv
    @6
    @14
    vy
    vx
    cr
    vy
    vx
    weq
    #
    @6
    @1
    @9
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
    @14
    @15
    @3
    @16
    vi
    vl
    cZ
    @5
    @2
    @9
    @1
    cle
    breq2
    rexralbidv
    @17
    @13
    vi
    vj
    cZ
    vi
    vj
    weq
    #
    @17
    @16
    vl
    @12
    wral
    @13
    @18
    @16
    vl
    @5
    @12
    @4
    @11
    cuz
    fveq2
    raleqdv
    @16
    @10
    vl
    vk
    @12
    vk
    @1
    @9
    cle
    vk
    @0
    cF
    xlimmnf.k
    vk
    @0
    nfcv
    nffv
    vk
    cle
    nfcv
    vk
    @9
    nfcv
    nfbr
    @10
    vl
    nfv
    vl
    vk
    weq
    @1
    @8
    @9
    cle
    @0
    @7
    cF
    fveq2
    breq1d
    cbvral
    syl6bb
    cbvrexv
    syl6bb
    cbvralv
    syl6bb
end
