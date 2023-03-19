include "cz.mm"
include "wcel.mm"
include "cli.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cop.mm"
include "wex.mm"
include "eldm2g.mm"
include "ibi.mm"
include "df-br.mm"
include "wa.mm"
include "cc.mm"
include "c2.mm"
include "cdiv.mm"
include "simpll.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "eqidd.mm"
include "simplr.mm"
include "climi.mm"
include "wi.mm"
include "eluzelz.mm"
include "uzid.mm"
include "syl.mm"
include "eleq2s.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "cr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "simpllr.mm"
include "climcl.mm"
include "simprl.mm"
include "simplrl.mm"
include "simplll.mm"
include "simprr.mm"
include "abssubd.mm"
include "simplrr.mm"
include "eqbrtrd.mm"
include "abs3lemd.mm"
include "ex.mm"
include "ralimdv.mm"
include "com23.mm"
include "syl2anc.mm"
include "mpdd.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "syl5bir.mm"
include "exlimdv.mm"
include "syl5.mm"
include "imp.mm"

theorem climcau
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume climcau.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint F y
  disjoint M y
  disjoint Z y
  assert |- ( ( M e. ZZ /\ F e. dom ~~> ) -> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x )

  proof
    cM
    cz
    wcel
    #
    cF
    cli
    cdm
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    vj
    cv
    #
    cF
    cfv
    #
    cmin
    co
    cabs
    cfv
    vx
    cv
    #
    clt
    wbr
    #
    vk
    @5
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
    @2
    cF
    vy
    cv
    #
    cop
    cli
    wcel
    #
    vy
    wex
    #
    @0
    @12
    @2
    @15
    vy
    cF
    cli
    @1
    eldm2g
    ibi
    @0
    @14
    @12
    vy
    @14
    cF
    @13
    cli
    wbr
    #
    @0
    @12
    cF
    @13
    cli
    df-br
    @0
    @16
    @12
    @0
    @16
    wa
    #
    @11
    vx
    crp
    @17
    @7
    crp
    wcel
    #
    wa
    #
    @4
    cc
    wcel
    #
    @4
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    @11
    @19
    @13
    @4
    @23
    vj
    vk
    cF
    cM
    cZ
    climcau.1
    @0
    @16
    @18
    simpll
    @18
    @23
    crp
    wcel
    @17
    @7
    rphalfcl
    adantl
    @19
    @3
    cZ
    wcel
    wa
    @4
    eqidd
    @0
    @16
    @18
    simplr
    climi
    @19
    @26
    @10
    vj
    cZ
    @19
    @5
    cZ
    wcel
    #
    wa
    #
    @26
    @6
    cc
    wcel
    #
    @6
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    @23
    clt
    wbr
    #
    wa
    #
    @10
    @28
    @5
    @9
    wcel
    #
    @26
    @33
    wi
    @27
    @34
    @19
    @34
    @5
    cM
    cuz
    cfv
    #
    cZ
    @5
    @35
    wcel
    @5
    cz
    wcel
    @34
    cM
    @5
    eluzelz
    @5
    uzid
    syl
    climcau.1
    eleq2s
    adantl
    @25
    @33
    vk
    @5
    @9
    vk
    vj
    weq
    #
    @20
    @29
    @24
    @32
    @36
    @4
    @6
    cc
    @3
    @5
    cF
    fveq2
    #
    eleq1d
    @36
    @22
    @31
    @23
    clt
    @36
    @21
    @30
    cabs
    @36
    @4
    @6
    @13
    cmin
    @37
    oveq1d
    fveq2d
    breq1d
    anbi12d
    rspcv
    syl
    @28
    @7
    cr
    wcel
    #
    @13
    cc
    wcel
    #
    @26
    @33
    @10
    wi
    wi
    @18
    @38
    @17
    @27
    @7
    rpre
    ad2antlr
    @28
    @16
    @39
    @0
    @16
    @18
    @27
    simpllr
    @13
    cF
    climcl
    syl
    @38
    @39
    wa
    #
    @33
    @26
    @10
    @40
    @33
    @26
    @10
    wi
    @40
    @33
    wa
    #
    @25
    @8
    vk
    @9
    @41
    @25
    @8
    @41
    @25
    wa
    #
    @4
    @6
    @13
    @7
    @41
    @20
    @24
    simprl
    @40
    @29
    @32
    @25
    simplrl
    #
    @38
    @39
    @33
    @25
    simpllr
    #
    @38
    @39
    @33
    @25
    simplll
    @41
    @20
    @24
    simprr
    @42
    @13
    @6
    cmin
    co
    cabs
    cfv
    @31
    @23
    clt
    @42
    @13
    @6
    @44
    @43
    abssubd
    @40
    @29
    @32
    @25
    simplrr
    eqbrtrd
    abs3lemd
    ex
    ralimdv
    ex
    com23
    syl2anc
    mpdd
    reximdva
    mpd
    ralrimiva
    ex
    syl5bir
    exlimdv
    syl5
    imp
end
