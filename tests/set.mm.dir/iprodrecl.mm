include "cprod.mm"
include "cmul.mm"
include "cseq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "iprodclim2.mm"
include "cr.mm"
include "cfv.mm"
include "eqeltrd.mm"
include "co.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqf.mm"
include "ffvelrnda.mm"
include "climrecl.mm"

theorem iprodrecl
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume iprodcl.1: |- Z = ( ZZ>= ` M )
  assume iprodcl.2: |- ( ph -> M e. ZZ )
  assume iprodcl.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprodcl.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iprodrecl.5: |- ( ( ph /\ k e. Z ) -> A e. RR )

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
  disjoint A j
  disjoint F j
  disjoint F x
  disjoint j k
  disjoint j ph
  disjoint k x
  disjoint M j
  disjoint M x
  disjoint ph x
  disjoint Z j
  assert |- ( ph -> prod_ k e. Z A e. RR )

  proof
    wph
    cZ
    cA
    vk
    cprod
    vj
    cmul
    cF
    cM
    cseq
    #
    cM
    cZ
    iprodcl.1
    iprodcl.2
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
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    #
    cA
    iprodrecl.5
    recnd
    iprodclim2
    wph
    cZ
    cr
    vj
    cv
    @0
    wph
    vk
    vx
    cmul
    cr
    cF
    cM
    cZ
    iprodcl.1
    iprodcl.2
    @2
    @1
    cF
    cfv
    cA
    cr
    iprodcl.4
    iprodrecl.5
    eqeltrd
    @1
    cr
    wcel
    vx
    cv
    #
    cr
    wcel
    wa
    @1
    @3
    cmul
    co
    cr
    wcel
    wph
    @1
    @3
    remulcl
    adantl
    seqf
    ffvelrnda
    climrecl
end
