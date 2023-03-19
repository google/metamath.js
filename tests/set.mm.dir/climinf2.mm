include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "breq1.mm"
include "ralbidv.mm"
include "wb.mm"
include "breq2d.mm"
include "cbvral.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrex.mm"
include "sylib.mm"
include "climinf2lem.mm"

theorem climinf2
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  assume climinf2.k: |- F/ k ph
  assume climinf2.n: |- F/_ k F
  assume climinf2.z: |- Z = ( ZZ>= ` M )
  assume climinf2.m: |- ( ph -> M e. ZZ )
  assume climinf2.f: |- ( ph -> F : Z --> RR )
  assume climinf2.l: |- ( ( ph /\ k e. Z ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climinf2.e: |- ( ph -> E. x e. RR A. k e. Z x <_ ( F ` k ) )

  disjoint F x
  disjoint Z k
  disjoint Z x
  disjoint k x
  disjoint F j
  disjoint F y
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint Z j
  disjoint Z y
  disjoint j k
  disjoint k y
  disjoint j ph
  disjoint ph y
  assert |- ( ph -> F ~~> inf ( ran F , RR* , < ) )

  proof
    wph
    vy
    vj
    cF
    cM
    cZ
    climinf2.z
    climinf2.m
    climinf2.f
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @0
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @7
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    vk
    vj
    @9
    @13
    vk
    wph
    @8
    vk
    climinf2.k
    @8
    vk
    nfv
    nfan
    vk
    @11
    @12
    cle
    vk
    @10
    cF
    climinf2.n
    vk
    @10
    nfcv
    nffv
    vk
    cle
    nfcv
    #
    vk
    @7
    cF
    climinf2.n
    vk
    @7
    nfcv
    nffv
    #
    nfbr
    nfim
    @0
    @7
    wceq
    #
    @2
    @9
    @6
    @13
    @16
    @1
    @8
    wph
    @0
    @7
    cZ
    eleq1
    anbi2d
    @16
    @4
    @11
    @5
    @12
    cle
    @16
    @3
    @10
    cF
    @0
    @7
    c1
    caddc
    oveq1
    fveq2d
    @0
    @7
    cF
    fveq2
    #
    breq12d
    imbi12d
    climinf2.l
    chvar
    wph
    vx
    cv
    #
    @5
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    vy
    cv
    #
    @12
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    climinf2.e
    @20
    @23
    vx
    vy
    cr
    @20
    vy
    nfv
    @23
    vx
    nfv
    @18
    @21
    wceq
    #
    @20
    @21
    @5
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    @23
    @24
    @19
    @25
    vk
    cZ
    @18
    @21
    @5
    cle
    breq1
    ralbidv
    @26
    @23
    wb
    @24
    @25
    @22
    vk
    vj
    cZ
    @25
    vj
    nfv
    vk
    @21
    @12
    cle
    vk
    @21
    nfcv
    @14
    @15
    nfbr
    @16
    @5
    @12
    @21
    cle
    @17
    breq2d
    cbvral
    a1i
    bitrd
    cbvrex
    sylib
    climinf2lem
end
