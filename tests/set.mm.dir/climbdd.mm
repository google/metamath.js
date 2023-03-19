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
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cuz.mm"
include "crp.mm"
include "simp3.mm"
include "climcau.mm"
include "3adant3.mm"
include "caubnd.mm"
include "syl2anc.mm"
include "wi.mm"
include "wa.mm"
include "r19.26.mm"
include "simpr.mm"
include "abscld.mm"
include "simpllr.mm"
include "ltle.mm"
include "expimpd.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "exp4b.mm"
include "com23.mm"
include "3impia.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem climbdd
  let vx: setvar x
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  assume climcau.1: |- Z = ( ZZ>= ` M )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M k
  disjoint M x
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k y
  disjoint x y
  disjoint F y
  disjoint M j
  disjoint M y
  disjoint Z j
  disjoint Z y
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
    @3
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
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    @7
    @8
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
    @5
    @3
    vj
    cv
    #
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    vk
    @14
    cuz
    cfv
    wral
    vj
    cZ
    wrex
    vy
    crp
    wral
    #
    @11
    @0
    @1
    @5
    simp3
    @0
    @1
    @15
    @5
    vy
    vj
    vk
    cF
    cM
    cZ
    climcau.1
    climcau
    3adant3
    vy
    vx
    vj
    vk
    cF
    cM
    cZ
    climcau.1
    caubnd
    syl2anc
    @6
    @10
    @13
    vx
    cr
    @0
    @1
    @5
    @8
    cr
    wcel
    #
    @10
    @13
    wi
    #
    wi
    @0
    @1
    wa
    #
    @16
    @5
    @17
    @18
    @16
    @5
    @10
    @13
    @5
    @10
    wa
    @4
    @9
    wa
    #
    vk
    cZ
    wral
    @18
    @16
    wa
    #
    @13
    @4
    @9
    vk
    cZ
    r19.26
    @20
    @19
    @12
    vk
    cZ
    @20
    @2
    cZ
    wcel
    #
    wa
    #
    @4
    @9
    @12
    @22
    @4
    wa
    #
    @7
    cr
    wcel
    @16
    @9
    @12
    wi
    @23
    @3
    @22
    @4
    simpr
    abscld
    @18
    @16
    @21
    @4
    simpllr
    @7
    @8
    ltle
    syl2anc
    expimpd
    ralimdva
    syl5bir
    exp4b
    com23
    3impia
    reximdvai
    mpd
end
