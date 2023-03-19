include "cur.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "wcel.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cio.mm"
include "eqid.mm"
include "dfur2.mm"
include "eleqtrd.mm"
include "jca.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidva.mm"
include "mpbid.mm"
include "weu.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "eleq2d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "rspcdv.mm"
include "mpd.mm"
include "adantrr.mm"
include "simprr.mm"
include "oveq2.mm"
include "id.mm"
include "oveq1.mm"
include "rspcva.mm"
include "simprd.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "ex.mm"
include "sylbird.mm"
include "alrimiv.mm"
include "eleq1.mm"
include "ralbidv.mm"
include "eqeu.mm"
include "syl121anc.mm"
include "iota2.mm"
include "mpbi2and.mm"
include "syl5req.mm"

theorem rngurd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let ve: setvar e
  assume rngurd.b: |- ( ph -> B = ( Base ` R ) )
  assume rngurd.p: |- ( ph -> .x. = ( .r ` R ) )
  assume rngurd.z: |- ( ph -> .1. e. B )
  assume rngurd.i: |- ( ( ph /\ x e. B ) -> ( .1. .x. x ) = x )
  assume rngurd.j: |- ( ( ph /\ x e. B ) -> ( x .x. .1. ) = x )

  disjoint B x
  disjoint R x
  disjoint .1. x
  disjoint .x. x
  disjoint ph x
  disjoint e x
  disjoint R e
  disjoint .1. e
  disjoint e ph
  assert |- ( ph -> .1. = ( 1r ` R ) )

  proof
    wph
    cR
    cur
    cfv
    #
    ve
    cv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    @1
    vx
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @4
    wceq
    #
    @4
    @1
    @5
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    @2
    wral
    #
    wa
    #
    ve
    cio
    #
    c.1
    vx
    @2
    cR
    @5
    @0
    ve
    @2
    eqid
    @5
    eqid
    @0
    eqid
    dfur2
    wph
    c.1
    @2
    wcel
    #
    c.1
    @4
    @5
    co
    #
    @4
    wceq
    #
    @4
    c.1
    @5
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    @2
    wral
    #
    @13
    c.1
    wceq
    #
    wph
    c.1
    cB
    @2
    rngurd.z
    rngurd.b
    eleqtrd
    #
    wph
    c.1
    @4
    c.x
    co
    #
    @4
    wceq
    #
    @4
    c.1
    c.x
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    cB
    wral
    @20
    wph
    @27
    vx
    cB
    wph
    @4
    cB
    wcel
    #
    wa
    #
    @24
    @26
    rngurd.i
    rngurd.j
    jca
    ralrimiva
    wph
    @27
    @19
    vx
    cB
    @2
    rngurd.b
    @29
    @24
    @16
    @26
    @18
    @29
    @23
    @15
    @4
    @29
    c.x
    @5
    c.1
    @4
    wph
    c.x
    @5
    wceq
    @28
    rngurd.p
    adantr
    #
    oveqd
    eqeq1d
    @29
    @25
    @17
    @4
    @29
    c.x
    @5
    @4
    c.1
    @30
    oveqd
    eqeq1d
    anbi12d
    raleqbidva
    mpbid
    #
    wph
    c.1
    cB
    wcel
    #
    @12
    ve
    weu
    #
    @14
    @20
    wa
    #
    @21
    wb
    rngurd.z
    wph
    @14
    @14
    @20
    @12
    @1
    c.1
    wceq
    #
    wi
    #
    ve
    wal
    @33
    @22
    @22
    @31
    wph
    @36
    ve
    wph
    @12
    @1
    cB
    wcel
    #
    @1
    @4
    c.x
    co
    #
    @4
    wceq
    #
    @4
    @1
    c.x
    co
    #
    @4
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    #
    @35
    wph
    @37
    @3
    @43
    @11
    wph
    cB
    @2
    @1
    rngurd.b
    eleq2d
    wph
    @42
    @10
    vx
    cB
    @2
    rngurd.b
    @29
    @39
    @7
    @41
    @9
    @29
    @38
    @6
    @4
    @29
    c.x
    @5
    @1
    @4
    @30
    oveqd
    eqeq1d
    @29
    @40
    @8
    @4
    @29
    c.x
    @5
    @4
    @1
    @30
    oveqd
    eqeq1d
    anbi12d
    raleqbidva
    anbi12d
    wph
    @44
    @35
    wph
    @44
    wa
    #
    c.1
    @1
    c.x
    co
    #
    @1
    c.1
    wph
    @37
    @46
    @1
    wceq
    #
    @43
    wph
    @37
    wa
    #
    @24
    vx
    cB
    wral
    #
    @47
    wph
    @49
    @37
    wph
    @24
    vx
    cB
    rngurd.i
    ralrimiva
    adantr
    @48
    @24
    @47
    vx
    @1
    cB
    wph
    @37
    simpr
    @48
    @4
    @1
    wceq
    #
    wa
    #
    @23
    @46
    @4
    @1
    @51
    @4
    @1
    c.1
    c.x
    @48
    @50
    simpr
    #
    oveq2d
    @52
    eqeq12d
    rspcdv
    mpd
    adantrr
    @45
    @32
    @43
    @46
    c.1
    wceq
    #
    wph
    @32
    @44
    rngurd.z
    adantr
    wph
    @37
    @43
    simprr
    @32
    @43
    wa
    @1
    c.1
    c.x
    co
    #
    c.1
    wceq
    #
    @53
    @42
    @55
    @53
    wa
    vx
    c.1
    cB
    @4
    c.1
    wceq
    #
    @39
    @55
    @41
    @53
    @56
    @38
    @54
    @4
    c.1
    @4
    c.1
    @1
    c.x
    oveq2
    @56
    id
    #
    eqeq12d
    @56
    @40
    @46
    @4
    c.1
    @4
    c.1
    @1
    c.x
    oveq1
    @57
    eqeq12d
    anbi12d
    rspcva
    simprd
    syl2anc
    eqtr3d
    ex
    sylbird
    alrimiv
    @12
    @34
    ve
    c.1
    @2
    @35
    @3
    @14
    @11
    @20
    @1
    c.1
    @2
    eleq1
    @35
    @10
    @19
    vx
    @2
    @35
    @7
    @16
    @9
    @18
    @35
    @6
    @15
    @4
    @1
    c.1
    @4
    @5
    oveq1
    eqeq1d
    @35
    @8
    @17
    @4
    @1
    c.1
    @4
    @5
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    anbi12d
    #
    eqeu
    syl121anc
    @12
    @34
    ve
    c.1
    cB
    @58
    iota2
    syl2anc
    mpbi2and
    syl5req
end
