include "crg.mm"
include "wcel.mm"
include "crng.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "wrex.mm"
include "cdomn.mm"
include "csn.mm"
include "wo.mm"
include "eqid.mm"
include "isringrng.mm"
include "wb.mm"
include "domnring.mm"
include "anim1i.mm"
include "lidlrng.mm"
include "syl.mm"
include "ibar.mm"
include "bicomd.mm"
include "adantl.mm"
include "wn.mm"
include "cur.mm"
include "ressmulr.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "ralbidv.mm"
include "wne.mm"
include "wi.mm"
include "simp-4l.mm"
include "lidlbas.mm"
include "eleq1d.mm"
include "ibir.mm"
include "ad3antlr.mm"
include "biimpd.mm"
include "necon3bd.mm"
include "imp.mm"
include "jca.mm"
include "adantr.mm"
include "simpr.mm"
include "lidldomn1.mm"
include "syl3anc.mm"
include "sylbid.mm"
include "eleq2d.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "impancom.mm"
include "lidl1el.mm"
include "sylibd.mm"
include "orrd.mm"
include "zlidlring.mm"
include "simprbi.mm"
include "wreu.mm"
include "ringideu.mm"
include "reurex.mm"
include "cin.mm"
include "ressbas.mm"
include "ineq1.mm"
include "inidm.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "mpbird.mm"
include "jaod.mm"
include "impbid.mm"
include "bitrd.mm"
include "mpdan.mm"
include "syl5bb.mm"

theorem uzlidlring
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )
  assume zlidlring.b: |- B = ( Base ` R )
  assume zlidlring.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Domn /\ U e. L ) -> ( I e. Ring <-> ( U = { .0. } \/ U = B ) ) )

  proof
    cI
    crg
    wcel
    #
    cI
    crng
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    cmulr
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @2
    @4
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    cI
    cbs
    cfv
    #
    wral
    #
    vx
    @10
    wrex
    #
    wa
    #
    cR
    cdomn
    wcel
    #
    cU
    cL
    wcel
    #
    wa
    #
    cU
    c.0
    csn
    #
    wceq
    #
    cU
    cB
    wceq
    #
    wo
    #
    vx
    vy
    @10
    cI
    @4
    @10
    eqid
    @4
    eqid
    isringrng
    #
    @16
    @1
    @13
    @20
    wb
    @16
    cR
    crg
    wcel
    #
    @15
    wa
    #
    @1
    @14
    @22
    @15
    cR
    domnring
    #
    anim1i
    #
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlrng
    syl
    @16
    @1
    wa
    #
    @13
    @12
    @20
    @1
    @13
    @12
    wb
    @16
    @1
    @12
    @13
    @1
    @12
    ibar
    bicomd
    adantl
    @26
    @12
    @20
    @26
    @12
    @20
    @26
    @12
    wa
    #
    @18
    @19
    @27
    @18
    wn
    #
    cR
    cur
    cfv
    #
    cU
    wcel
    #
    @19
    @26
    @28
    @12
    @30
    @26
    @28
    wa
    #
    @11
    @30
    vx
    @10
    @31
    @2
    @10
    wcel
    #
    wa
    #
    @11
    @30
    @33
    @11
    wa
    @2
    @29
    cU
    @33
    @11
    @2
    @29
    wceq
    #
    @33
    @11
    @2
    @3
    cR
    cmulr
    cfv
    #
    co
    #
    @3
    wceq
    #
    @3
    @2
    @35
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @10
    wral
    #
    @34
    @33
    @9
    @40
    vy
    @10
    @26
    @9
    @40
    wb
    #
    @28
    @32
    @15
    @42
    @14
    @1
    @15
    @6
    @37
    @8
    @39
    @15
    @5
    @36
    @3
    @15
    @4
    @35
    @2
    @3
    @15
    @35
    @4
    cU
    cR
    cI
    @35
    cL
    lidlabl.i
    @35
    eqid
    #
    ressmulr
    eqcomd
    #
    oveqd
    eqeq1d
    @15
    @7
    @38
    @3
    @15
    @4
    @35
    @3
    @2
    @44
    oveqd
    eqeq1d
    anbi12d
    #
    ad2antlr
    ad2antrr
    ralbidv
    @33
    @14
    @10
    cL
    wcel
    #
    @10
    @17
    wne
    #
    wa
    #
    @32
    @41
    @34
    wi
    @14
    @15
    @1
    @28
    @32
    simp-4l
    @31
    @48
    @32
    @31
    @46
    @47
    @15
    @46
    @14
    @1
    @28
    @15
    @46
    @15
    @10
    cU
    cL
    cR
    cU
    cI
    cL
    lidlabl.l
    lidlabl.i
    lidlbas
    #
    eleq1d
    ibir
    ad3antlr
    @26
    @28
    @47
    @26
    @18
    @10
    @17
    @26
    @10
    @17
    wceq
    @18
    @26
    @10
    cU
    @17
    @15
    @10
    cU
    wceq
    #
    @14
    @1
    @49
    ad2antlr
    eqeq1d
    biimpd
    necon3bd
    imp
    jca
    adantr
    @31
    @32
    simpr
    vy
    cR
    @35
    @10
    @29
    @2
    cL
    c.0
    lidlabl.l
    @43
    @29
    eqid
    #
    zlidlring.0
    lidldomn1
    syl3anc
    sylbid
    imp
    @33
    @2
    cU
    wcel
    #
    @11
    @31
    @32
    @52
    @31
    @32
    @52
    @31
    @10
    cU
    @2
    @15
    @50
    @14
    @1
    @28
    @49
    ad3antlr
    eleq2d
    biimpd
    imp
    adantr
    eqeltrrd
    ex
    rexlimdva
    impancom
    @26
    @30
    @19
    wb
    #
    @12
    @26
    @23
    @53
    @16
    @23
    @1
    @25
    adantr
    cB
    cR
    cL
    @29
    cU
    lidlabl.l
    zlidlring.b
    @51
    lidl1el
    syl
    adantr
    sylibd
    orrd
    ex
    @26
    @18
    @12
    @19
    @14
    @18
    @12
    wi
    #
    @15
    @1
    @14
    @22
    @54
    @24
    @22
    @18
    @12
    @22
    @18
    wa
    @0
    @12
    cB
    cR
    cU
    cI
    cL
    c.0
    lidlabl.l
    lidlabl.i
    zlidlring.b
    zlidlring.0
    zlidlring
    @0
    @1
    @12
    @21
    simprbi
    syl
    ex
    syl
    ad2antrr
    @26
    @23
    @1
    wa
    #
    @19
    @12
    wi
    @16
    @23
    @1
    @25
    anim1i
    @55
    @19
    @12
    @55
    @19
    wa
    #
    @12
    @40
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    @23
    @58
    @1
    @19
    @22
    @58
    @15
    @22
    @57
    vx
    cB
    wreu
    @58
    vy
    vx
    cB
    cR
    @35
    zlidlring.b
    @43
    ringideu
    @57
    vx
    cB
    reurex
    syl
    adantr
    ad2antrr
    @56
    @11
    @57
    vx
    @10
    cB
    @56
    cU
    cB
    cin
    #
    @10
    cB
    @15
    @59
    @10
    wceq
    @22
    @1
    @19
    cU
    cB
    cI
    cL
    cR
    lidlabl.i
    zlidlring.b
    ressbas
    ad3antlr
    @19
    @59
    cB
    wceq
    @55
    @19
    @59
    cB
    cB
    cin
    cB
    cU
    cB
    cB
    ineq1
    cB
    inidm
    syl6eq
    adantl
    eqtr3d
    #
    @56
    @9
    @40
    vy
    @10
    cB
    @60
    @15
    @42
    @22
    @1
    @19
    @45
    ad3antlr
    raleqbidv
    rexeqbidv
    mpbird
    ex
    syl
    jaod
    impbid
    bitrd
    mpdan
    syl5bb
end
