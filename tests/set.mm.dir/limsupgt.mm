include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "clsp.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "limsupgtlem.mm"
include "wceq.mm"
include "wb.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfv.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "cbvral.mm"
include "a1i.mm"
include "raleqdv.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "sylib.mm"

theorem limsupgt
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
  assume limsupgt.k: |- F/_ k F
  assume limsupgt.m: |- ( ph -> M e. ZZ )
  assume limsupgt.z: |- Z = ( ZZ>= ` M )
  assume limsupgt.f: |- ( ph -> F : Z --> RR )
  assume limsupgt.r: |- ( ph -> ( limsup ` F ) e. RR )
  assume limsupgt.x: |- ( ph -> X e. RR+ )

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
  disjoint X i
  disjoint X l
  disjoint i k
  disjoint k l
  disjoint Z i
  disjoint Z l
  disjoint i ph
  disjoint l ph
  disjoint k x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) - X ) < ( limsup ` F ) )

  proof
    wph
    vl
    cv
    #
    cF
    cfv
    #
    cX
    cmin
    co
    #
    cF
    clsp
    cfv
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
    vk
    cv
    #
    cF
    cfv
    #
    cX
    cmin
    co
    #
    @3
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
    limsupgt.m
    limsupgt.z
    limsupgt.f
    limsupgt.r
    limsupgt.x
    limsupgtlem
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
    @11
    vk
    @6
    wral
    #
    @14
    @7
    @16
    wb
    @15
    @4
    @11
    vl
    vk
    @6
    vk
    @2
    @3
    clt
    vk
    @1
    cX
    cmin
    vk
    @0
    cF
    limsupgt.k
    vk
    @0
    nfcv
    nffv
    vk
    cmin
    nfcv
    vk
    cX
    nfcv
    nfov
    vk
    clt
    nfcv
    vk
    cF
    clsp
    vk
    clsp
    nfcv
    limsupgt.k
    nffv
    nfbr
    @11
    vl
    nfv
    @0
    @8
    wceq
    #
    @2
    @10
    @3
    clt
    @17
    @1
    @9
    cX
    cmin
    @0
    @8
    cF
    fveq2
    oveq1d
    breq1d
    cbvral
    a1i
    @15
    @11
    vk
    @6
    @13
    @5
    @12
    cuz
    fveq2
    raleqdv
    bitrd
    cbvrexv
    sylib
end
