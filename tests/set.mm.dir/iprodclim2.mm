include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "cprod.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "cc.mm"
include "eqeltrd.mm"
include "ntrivcvg.mm"
include "climdm.mm"
include "sylib.mm"
include "iprod.mm"
include "breqtrrd.mm"

theorem iprodclim2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume iprodclim.1: |- Z = ( ZZ>= ` M )
  assume iprodclim.2: |- ( ph -> M e. ZZ )
  assume iprodclim.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprodclim.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iprodclim.5: |- ( ( ph /\ k e. Z ) -> A e. CC )

  disjoint A n
  disjoint A y
  disjoint F k
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z k
  disjoint Z n
  disjoint Z y
  disjoint F n
  disjoint F y
  disjoint M n
  assert |- ( ph -> seq M ( x. , F ) ~~> prod_ k e. Z A )

  proof
    wph
    cmul
    cF
    cM
    cseq
    #
    @0
    cli
    cfv
    #
    cZ
    cA
    vk
    cprod
    cli
    wph
    @0
    cli
    cdm
    wcel
    @0
    @1
    cli
    wbr
    wph
    vy
    vk
    vn
    cF
    cM
    cZ
    iprodclim.1
    iprodclim.3
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    @2
    cF
    cfv
    cA
    cc
    iprodclim.4
    iprodclim.5
    eqeltrd
    ntrivcvg
    @0
    climdm
    sylib
    wph
    vy
    cA
    vk
    vn
    cF
    cM
    cZ
    iprodclim.1
    iprodclim.2
    iprodclim.3
    iprodclim.4
    iprodclim.5
    iprod
    breqtrrd
end
