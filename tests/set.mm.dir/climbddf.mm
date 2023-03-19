include "cz.mm"
include "wcel.mm"
include "cli.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wral.mm"
include "w3a.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2.mm"
include "nfv.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfel.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "climbdd.mm"
include "syl3anc.mm"
include "nfbr.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexbii.mm"
include "sylib.mm"

theorem climbddf
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climbddf.1: |- F/_ k F
  assume climbddf.2: |- Z = ( ZZ>= ` M )

  disjoint F x
  disjoint M k
  disjoint M x
  disjoint k x
  disjoint Z k
  disjoint Z x
  disjoint F j
  disjoint j x
  disjoint M j
  disjoint j k
  disjoint Z j
  assert |- ( ( M e. ZZ /\ F e. dom ~~> /\ A. k e. Z ( F ` k ) e. CC ) -> E. x e. RR A. k e. Z ( abs ` ( F ` k ) ) <_ x )

  proof
    cM
    cz
    wcel
    #
    cF
    cli
    cdm
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    vk
    cZ
    wral
    #
    w3a
    #
    vj
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @3
    cabs
    cfv
    #
    @10
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
    @6
    @0
    @1
    @8
    cc
    wcel
    #
    vj
    cZ
    wral
    #
    @13
    @0
    @1
    @5
    simp1
    @0
    @1
    @5
    simp2
    @5
    @0
    @18
    @1
    @5
    @18
    @4
    @17
    vk
    vj
    cZ
    @4
    vj
    nfv
    vk
    @8
    cc
    vk
    @7
    cF
    climbddf.1
    vk
    @7
    nfcv
    nffv
    #
    vk
    cc
    nfcv
    nfel
    @2
    @7
    wceq
    @3
    @8
    cc
    @2
    @7
    cF
    fveq2
    eleq1d
    cbvral
    biimpi
    3ad2ant3
    vx
    vj
    cF
    cM
    cZ
    climbddf.2
    climbdd
    syl3anc
    @12
    @16
    vx
    cr
    @11
    @15
    vj
    vk
    cZ
    vk
    @9
    @10
    cle
    vk
    @8
    cabs
    vk
    cabs
    nfcv
    @19
    nffv
    vk
    cle
    nfcv
    vk
    @10
    nfcv
    nfbr
    @15
    vj
    nfv
    @7
    @2
    wceq
    #
    @9
    @14
    @10
    cle
    @20
    @8
    @3
    cabs
    @7
    @2
    cF
    fveq2
    fveq2d
    breq1d
    cbvral
    rexbii
    sylib
end
