include "clsi.mm"
include "cfv.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "liminfltlem.mm"
include "wceq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "wb.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfv.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "sylib.mm"

theorem liminflt
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let vl: setvar l
  let vx: setvar x
  assume liminflt.k: |- F/_ k F
  assume liminflt.m: |- ( ph -> M e. ZZ )
  assume liminflt.z: |- Z = ( ZZ>= ` M )
  assume liminflt.f: |- ( ph -> F : Z --> RR )
  assume liminflt.r: |- ( ph -> ( liminf ` F ) e. RR )
  assume liminflt.x: |- ( ph -> X e. RR+ )

  disjoint F j
  disjoint X j
  disjoint X k
  disjoint j k
  disjoint Z j
  disjoint F i
  disjoint F l
  disjoint i j
  disjoint i l
  disjoint j l
  disjoint M l
  disjoint X i
  disjoint X l
  disjoint i k
  disjoint k l
  disjoint Z i
  disjoint Z l
  disjoint i ph
  disjoint l ph
  disjoint k x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( liminf ` F ) < ( ( F ` k ) + X ) )

  proof
    wph
    cF
    clsi
    cfv
    #
    vl
    cv
    #
    cF
    cfv
    #
    cX
    caddc
    co
    #
    clt
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
    @0
    vk
    cv
    #
    cF
    cfv
    #
    cX
    caddc
    co
    #
    clt
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
    wph
    vi
    vl
    cF
    cM
    cX
    cZ
    liminflt.m
    liminflt.z
    liminflt.f
    liminflt.r
    liminflt.x
    liminfltlem
    @7
    @14
    vi
    vj
    cZ
    @5
    @12
    wceq
    #
    @7
    @4
    vl
    @13
    wral
    #
    @14
    @15
    @4
    vl
    @6
    @13
    @5
    @12
    cuz
    fveq2
    raleqdv
    @16
    @14
    wb
    @15
    @4
    @11
    vl
    vk
    @13
    vk
    @0
    @3
    clt
    vk
    cF
    clsi
    vk
    clsi
    nfcv
    liminflt.k
    nffv
    vk
    clt
    nfcv
    vk
    @2
    cX
    caddc
    vk
    @1
    cF
    liminflt.k
    vk
    @1
    nfcv
    nffv
    vk
    caddc
    nfcv
    vk
    cX
    nfcv
    nfov
    nfbr
    @11
    vl
    nfv
    @1
    @8
    wceq
    #
    @3
    @10
    @0
    clt
    @17
    @2
    @9
    cX
    caddc
    @1
    @8
    cF
    fveq2
    oveq1d
    breq2d
    cbvral
    a1i
    bitrd
    cbvrexv
    sylib
end
