include "cv.mm"
include "wne.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "fphpd.mm"
include "wcel.mm"
include "wo.mm"
include "cr.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantr.mm"
include "adantrl.mm"
include "lttri2d.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simpr.mm"
include "simplr.mm"
include "weq.mm"
include "breq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "eqeq2d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "ex.mm"
include "eqcomd.mm"
include "jaod.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "anim2d.mm"
include "reximdva.mm"
include "syld.mm"
include "sylbid.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem fphpdo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vb: setvar b
  let vc: setvar c
  assume fphpdo.1: |- ( ph -> A C_ RR )
  assume fphpdo.2: |- ( ph -> B e. _V )
  assume fphpdo.3: |- ( ph -> B ~< A )
  assume fphpdo.4: |- ( ( ph /\ z e. A ) -> C e. B )
  assume fphpdo.5: |- ( z = x -> C = D )
  assume fphpdo.6: |- ( z = y -> C = E )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D y
  disjoint D z
  disjoint E x
  disjoint E z
  disjoint b ph
  disjoint c ph
  disjoint b x
  disjoint c x
  disjoint b y
  disjoint c y
  disjoint b z
  disjoint c z
  disjoint b c
  disjoint A b
  disjoint A c
  disjoint B b
  disjoint B c
  disjoint C b
  disjoint C c
  disjoint D b
  disjoint D c
  disjoint E b
  disjoint E c
  assert |- ( ph -> E. x e. A E. y e. A ( x < y /\ D = E ) )

  proof
    wph
    vb
    cv
    #
    vc
    cv
    #
    wne
    #
    @0
    vz
    cA
    cC
    cmpt
    #
    cfv
    #
    @1
    @3
    cfv
    #
    wceq
    #
    wa
    #
    vc
    cA
    wrex
    vb
    cA
    wrex
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    cD
    cE
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    wph
    vb
    vc
    cA
    cB
    @4
    @5
    fphpdo.3
    wph
    cA
    cB
    @0
    @3
    wph
    vz
    cA
    cC
    cB
    @3
    fphpdo.4
    @3
    eqid
    #
    fmptd
    ffvelrnda
    @0
    @1
    @3
    fveq2
    fphpd
    wph
    @7
    @14
    vb
    vc
    cA
    cA
    wph
    @0
    cA
    wcel
    #
    @1
    cA
    wcel
    #
    wa
    #
    wa
    #
    @6
    @2
    @14
    @19
    @6
    @2
    @14
    @19
    @6
    wa
    #
    @2
    @0
    @1
    clt
    wbr
    #
    @1
    @0
    clt
    wbr
    #
    wo
    #
    @14
    @20
    @0
    @1
    @19
    @0
    cr
    wcel
    #
    @6
    wph
    @16
    @24
    @17
    wph
    cA
    cr
    @0
    fphpdo.1
    sselda
    adantrr
    adantr
    @19
    @1
    cr
    wcel
    #
    @6
    wph
    @17
    @25
    @16
    wph
    cA
    cr
    @1
    fphpdo.1
    sselda
    adantrl
    adantr
    lttri2d
    @20
    @23
    @10
    @8
    @3
    cfv
    #
    @9
    @3
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    @14
    @20
    @21
    @31
    @22
    @20
    @21
    @31
    @20
    @21
    wa
    @16
    @17
    @21
    @6
    @31
    @19
    @16
    @6
    @21
    wph
    @16
    @17
    simprl
    #
    ad2antrr
    @19
    @17
    @6
    @21
    wph
    @16
    @17
    simprr
    #
    ad2antrr
    @20
    @21
    simpr
    @19
    @6
    @21
    simplr
    @29
    @21
    @6
    wa
    @0
    @9
    clt
    wbr
    #
    @4
    @27
    wceq
    #
    wa
    vx
    vy
    @0
    @1
    cA
    cA
    vx
    vb
    weq
    #
    @10
    @34
    @28
    @35
    @8
    @0
    @9
    clt
    breq1
    @36
    @26
    @4
    @27
    @8
    @0
    @3
    fveq2
    eqeq1d
    anbi12d
    vy
    vc
    weq
    #
    @34
    @21
    @35
    @6
    @9
    @1
    @0
    clt
    breq2
    @37
    @27
    @5
    @4
    @9
    @1
    @3
    fveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    ex
    @20
    @22
    @31
    @20
    @22
    wa
    #
    @17
    @16
    @22
    @5
    @4
    wceq
    #
    @31
    @19
    @17
    @6
    @22
    @33
    ad2antrr
    @19
    @16
    @6
    @22
    @32
    ad2antrr
    @20
    @22
    simpr
    @38
    @4
    @5
    @19
    @6
    @22
    simplr
    eqcomd
    @29
    @22
    @39
    wa
    @1
    @9
    clt
    wbr
    #
    @5
    @27
    wceq
    #
    wa
    vx
    vy
    @1
    @0
    cA
    cA
    vx
    vc
    weq
    #
    @10
    @40
    @28
    @41
    @8
    @1
    @9
    clt
    breq1
    @42
    @26
    @5
    @27
    @8
    @1
    @3
    fveq2
    eqeq1d
    anbi12d
    vy
    vb
    weq
    #
    @40
    @22
    @41
    @39
    @9
    @0
    @1
    clt
    breq2
    @43
    @27
    @4
    @5
    @9
    @0
    @3
    fveq2
    eqeq2d
    anbi12d
    rspc2ev
    syl112anc
    ex
    jaod
    wph
    @31
    @14
    wi
    @18
    @6
    wph
    @30
    @13
    vx
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    @29
    @12
    vy
    cA
    @45
    @9
    cA
    wcel
    #
    wa
    #
    @28
    @11
    @10
    @47
    @28
    @11
    @47
    @26
    cD
    @27
    cE
    @47
    @44
    cD
    cB
    wcel
    #
    @26
    cD
    wceq
    wph
    @44
    @46
    simplr
    @45
    @48
    @46
    wph
    vz
    cv
    #
    cA
    wcel
    #
    wa
    #
    cC
    cB
    wcel
    #
    wi
    #
    @45
    @48
    wi
    vz
    vx
    vz
    vx
    weq
    #
    @51
    @45
    @52
    @48
    @54
    @50
    @44
    wph
    @49
    @8
    cA
    eleq1
    anbi2d
    @54
    cC
    cD
    cB
    fphpdo.5
    eleq1d
    imbi12d
    fphpdo.4
    chvarv
    adantr
    vz
    @8
    cC
    cD
    cA
    cB
    @3
    fphpdo.5
    @15
    fvmptg
    syl2anc
    @47
    @46
    cE
    cB
    wcel
    #
    @27
    cE
    wceq
    @45
    @46
    simpr
    wph
    @46
    @55
    @44
    @53
    wph
    @46
    wa
    #
    @55
    wi
    vz
    vy
    vz
    vy
    weq
    #
    @51
    @56
    @52
    @55
    @57
    @50
    @46
    wph
    @49
    @9
    cA
    eleq1
    anbi2d
    @57
    cC
    cE
    cB
    fphpdo.6
    eleq1d
    imbi12d
    fphpdo.4
    chvarv
    adantlr
    vz
    @9
    cC
    cE
    cA
    cB
    @3
    fphpdo.6
    @15
    fvmptg
    syl2anc
    eqeq12d
    biimpd
    anim2d
    reximdva
    reximdva
    ad2antrr
    syld
    sylbid
    expimpd
    ancomsd
    rexlimdvva
    mpd
end
