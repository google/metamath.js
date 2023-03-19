include "cprod.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "cfv.mm"
include "cc.mm"
include "iprod.mm"
include "cdm.mm"
include "wf.mm"
include "wcel.mm"
include "fclim.mm"
include "cv.mm"
include "wa.mm"
include "eqeltrd.mm"
include "ntrivcvg.mm"
include "ffvelrn.mm"
include "sylancr.mm"

theorem iprodcl
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume iprodcl.1: |- Z = ( ZZ>= ` M )
  assume iprodcl.2: |- ( ph -> M e. ZZ )
  assume iprodcl.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprodcl.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iprodcl.5: |- ( ( ph /\ k e. Z ) -> A e. CC )

  disjoint A n
  disjoint A y
  disjoint F k
  disjoint F n
  disjoint F y
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M n
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z k
  disjoint Z n
  disjoint Z y
  assert |- ( ph -> prod_ k e. Z A e. CC )

  proof
    wph
    cZ
    cA
    vk
    cprod
    cmul
    cF
    cM
    cseq
    #
    cli
    cfv
    #
    cc
    wph
    vy
    cA
    vk
    vn
    cF
    cM
    cZ
    iprodcl.1
    iprodcl.2
    iprodcl.3
    iprodcl.4
    iprodcl.5
    iprod
    wph
    cli
    cdm
    #
    cc
    cli
    wf
    @0
    @2
    wcel
    @1
    cc
    wcel
    fclim
    wph
    vy
    vk
    vn
    cF
    cM
    cZ
    iprodcl.1
    iprodcl.3
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    @3
    cF
    cfv
    cA
    cc
    iprodcl.4
    iprodcl.5
    eqeltrd
    ntrivcvg
    @2
    cc
    @0
    cli
    ffvelrn
    sylancr
    eqeltrd
end
