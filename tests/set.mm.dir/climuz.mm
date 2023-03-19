include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "climuzlem.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfv.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrexv.mm"
include "cbvralv.mm"
include "anbi2i.mm"

theorem climuz
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
  assume climuz.k: |- F/_ k F
  assume climuz.m: |- ( ph -> M e. ZZ )
  assume climuz.z: |- Z = ( ZZ>= ` M )
  assume climuz.f: |- ( ph -> F : Z --> CC )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F j
  disjoint F x
  disjoint Z j
  disjoint Z x
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
  disjoint M i
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint i ph
  disjoint l ph
  disjoint ph y
  assert |- ( ph -> ( F ~~> A <-> ( A e. CC /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - A ) ) < x ) ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    #
    vl
    cv
    #
    cF
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
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
    #
    vy
    crp
    wral
    #
    wa
    #
    @0
    vk
    cv
    #
    cF
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
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
    #
    vx
    crp
    wral
    #
    wa
    #
    wph
    vy
    cA
    vi
    vl
    cF
    cM
    cZ
    climuz.m
    climuz.z
    climuz.f
    climuzlem
    @12
    @24
    wb
    wph
    @11
    @23
    @0
    @10
    @22
    vy
    vx
    crp
    @5
    @17
    wceq
    #
    @10
    @4
    @17
    clt
    wbr
    #
    vl
    @8
    wral
    #
    vi
    cZ
    wrex
    #
    @22
    @25
    @9
    @27
    vi
    cZ
    @25
    @6
    @26
    vl
    @8
    @5
    @17
    @4
    clt
    breq2
    ralbidv
    rexbidv
    @28
    @22
    wb
    @25
    @27
    @21
    vi
    vj
    cZ
    @7
    @19
    wceq
    #
    @27
    @26
    vl
    @20
    wral
    #
    @21
    @29
    @26
    vl
    @8
    @20
    @7
    @19
    cuz
    fveq2
    raleqdv
    @30
    @21
    wb
    @29
    @26
    @18
    vl
    vk
    @20
    vk
    @4
    @17
    clt
    vk
    @3
    cabs
    vk
    cabs
    nfcv
    vk
    @2
    cA
    cmin
    vk
    @1
    cF
    climuz.k
    vk
    @1
    nfcv
    nffv
    vk
    cmin
    nfcv
    vk
    cA
    nfcv
    nfov
    nffv
    vk
    clt
    nfcv
    vk
    @17
    nfcv
    nfbr
    @18
    vl
    nfv
    @1
    @13
    wceq
    #
    @4
    @16
    @17
    clt
    @31
    @3
    @15
    cabs
    @31
    @2
    @14
    cA
    cmin
    @1
    @13
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    cbvral
    a1i
    bitrd
    cbvrexv
    a1i
    bitrd
    cbvralv
    anbi2i
    a1i
    bitrd
end
