include "cpnf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cr.mm"
include "xlimpnfv.mm"
include "weq.mm"
include "breq1.mm"
include "rexralbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq2d.mm"
include "cbvral.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "cbvralv.mm"

theorem xlimpnf
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
  assume xlimpnf.k: |- F/_ k F
  assume xlimpnf.m: |- ( ph -> M e. ZZ )
  assume xlimpnf.z: |- Z = ( ZZ>= ` M )
  assume xlimpnf.f: |- ( ph -> F : Z --> RR* )

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
  assert |- ( ph -> ( F ~~>* +oo <-> A. x e. RR E. j e. Z A. k e. ( ZZ>= ` j ) x <_ ( F ` k ) ) )

  proof
    wph
    cF
    cpnf
    clsxlim
    wbr
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
    wral
    vi
    cZ
    wrex
    #
    vy
    cr
    wral
    vx
    cv
    #
    vk
    cv
    #
    cF
    cfv
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
    xlimpnf.m
    xlimpnf.z
    xlimpnf.f
    xlimpnfv
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
    @7
    @2
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
    @0
    @7
    @2
    cle
    breq1
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
    @7
    @2
    cle
    vk
    @7
    nfcv
    vk
    cle
    nfcv
    vk
    @1
    cF
    xlimpnf.k
    vk
    @1
    nfcv
    nffv
    nfbr
    @10
    vl
    nfv
    vl
    vk
    weq
    @2
    @9
    @7
    cle
    @1
    @8
    cF
    fveq2
    breq2d
    cbvral
    syl6bb
    cbvrexv
    syl6bb
    cbvralv
    syl6bb
end
