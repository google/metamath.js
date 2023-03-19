include "cr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wrex.mm"
include "vex.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "elab2.mm"
include "wa.mm"
include "sselda.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "w3a.mm"
include "3jca.mm"
include "suprub.mm"
include "sylan.mm"
include "leadd1dd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wb.mm"
include "wi.mm"
include "readdcld.mm"
include "eleq1a.mm"
include "syl.mm"
include "ssrdv.mm"
include "wex.mm"
include "ovex.mm"
include "isseti.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "sylancl.mm"
include "exbii.mm"
include "n0.mm"
include "rexcom4.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "cmin.mm"
include "ltsubaddd.mm"
include "biimpar.mm"
include "resubcld.mm"
include "suprlub.mm"
include "mpbid.mm"
include "rspe.mm"
include "adantl.mm"
include "simplrr.mm"
include "adantlr.mm"
include "eqbrtrrd.mm"
include "mpdan.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpi.mm"
include "ad2antrr.mm"
include "lenltd.mm"
include "mtbird.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "eqleltd.mm"
include "mpbir2and.mm"
include "eqcomd.mm"

theorem supaddc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vb: setvar b
  let vw: setvar w
  let va: setvar a
  assume supadd.a1: |- ( ph -> A C_ RR )
  assume supadd.a2: |- ( ph -> A =/= (/) )
  assume supadd.a3: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume supaddc.b: |- ( ph -> B e. RR )
  assume supaddc.c: |- C = { z | E. v e. A z = ( v + B ) }

  disjoint x y
  disjoint x z
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint v y
  disjoint A y
  disjoint v z
  disjoint A z
  disjoint A v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B v
  disjoint C x
  disjoint ph z
  disjoint ph v
  disjoint b x
  disjoint w x
  disjoint a x
  disjoint b y
  disjoint w y
  disjoint a y
  disjoint b z
  disjoint w z
  disjoint a z
  disjoint b v
  disjoint b w
  disjoint a b
  disjoint A b
  disjoint v w
  disjoint a v
  disjoint a w
  disjoint A w
  disjoint A a
  disjoint B b
  disjoint B w
  disjoint B a
  disjoint C w
  disjoint C a
  disjoint b ph
  disjoint ph w
  disjoint a ph
  assert |- ( ph -> ( sup ( A , RR , < ) + B ) = sup ( C , RR , < ) )

  proof
    wph
    cC
    cr
    clt
    csup
    #
    cA
    cr
    clt
    csup
    #
    cB
    caddc
    co
    #
    wph
    @0
    @2
    wceq
    @0
    @2
    cle
    wbr
    #
    @0
    @2
    clt
    wbr
    #
    wn
    wph
    @3
    vw
    cv
    #
    @2
    cle
    wbr
    #
    vw
    cC
    wral
    #
    wph
    @6
    vw
    cC
    @5
    cC
    wcel
    #
    @5
    va
    cv
    #
    cB
    caddc
    co
    #
    wceq
    #
    va
    cA
    wrex
    #
    wph
    @6
    vz
    cv
    #
    vv
    cv
    #
    cB
    caddc
    co
    #
    wceq
    #
    vv
    cA
    wrex
    #
    @12
    vz
    @5
    cC
    vw
    vex
    @17
    @13
    @10
    wceq
    #
    va
    cA
    wrex
    vz
    vw
    weq
    #
    @12
    @16
    @18
    vv
    va
    cA
    vv
    va
    weq
    @15
    @10
    @13
    @14
    @9
    cB
    caddc
    oveq1
    eqeq2d
    cbvrexv
    @19
    @18
    @11
    va
    cA
    @13
    @5
    @10
    eqeq1
    rexbidv
    syl5bb
    supaddc.c
    elab2
    #
    wph
    @11
    @6
    va
    cA
    wph
    @9
    cA
    wcel
    #
    wa
    #
    @6
    @11
    @10
    @2
    cle
    wbr
    @22
    @9
    @1
    cB
    wph
    cA
    cr
    @9
    supadd.a1
    sselda
    #
    wph
    @1
    cr
    wcel
    #
    @21
    wph
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    @24
    supadd.a1
    supadd.a2
    supadd.a3
    vx
    vy
    cA
    suprcl
    syl3anc
    #
    adantr
    wph
    cB
    cr
    wcel
    #
    @21
    supaddc.b
    adantr
    #
    wph
    @25
    @26
    @28
    w3a
    @21
    @9
    @1
    cle
    wbr
    wph
    @25
    @26
    @28
    supadd.a1
    supadd.a2
    supadd.a3
    3jca
    vx
    vy
    cA
    @9
    suprub
    sylan
    leadd1dd
    @5
    @10
    @2
    cle
    breq1
    syl5ibrcom
    rexlimdva
    syl5bi
    ralrimiv
    #
    wph
    cC
    cr
    wss
    #
    cC
    c0
    wne
    #
    @5
    @27
    cle
    wbr
    #
    vw
    cC
    wral
    #
    vx
    cr
    wrex
    #
    @2
    cr
    wcel
    #
    @3
    @7
    wb
    wph
    vw
    cC
    cr
    @8
    @12
    wph
    @5
    cr
    wcel
    #
    @20
    wph
    @11
    @39
    va
    cA
    @22
    @10
    cr
    wcel
    #
    @11
    @39
    wi
    @22
    @9
    cB
    @23
    @31
    readdcld
    #
    @10
    cr
    @5
    eleq1a
    syl
    rexlimdva
    syl5bi
    ssrdv
    #
    wph
    @11
    vw
    wex
    #
    va
    cA
    wrex
    #
    @34
    wph
    @26
    @43
    va
    cA
    wral
    @44
    supadd.a2
    @43
    va
    cA
    vw
    @10
    @9
    cB
    caddc
    ovex
    isseti
    #
    rgenw
    @43
    va
    cA
    r19.2z
    sylancl
    @8
    vw
    wex
    @12
    vw
    wex
    @34
    @44
    @8
    @12
    vw
    @20
    exbii
    vw
    cC
    n0
    @11
    va
    vw
    cA
    rexcom4
    3bitr4i
    sylibr
    #
    wph
    @38
    @7
    @37
    wph
    @1
    cB
    @29
    supaddc.b
    readdcld
    #
    @32
    @36
    @7
    vx
    @2
    cr
    @27
    @2
    wceq
    @35
    @6
    vw
    cC
    @27
    @2
    @5
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    @47
    vx
    vw
    vw
    cC
    @2
    suprleub
    syl31anc
    mpbird
    wph
    @4
    @0
    cB
    cmin
    co
    #
    @9
    clt
    wbr
    #
    va
    cA
    wrex
    #
    wph
    @4
    wa
    #
    @49
    @1
    clt
    wbr
    #
    @51
    wph
    @53
    @4
    wph
    @0
    cB
    @1
    wph
    @33
    @34
    @37
    @0
    cr
    wcel
    #
    @42
    @46
    @48
    vx
    vw
    cC
    suprcl
    syl3anc
    #
    supaddc.b
    @29
    ltsubaddd
    biimpar
    wph
    @53
    @51
    wb
    #
    @4
    wph
    @25
    @26
    @28
    @49
    cr
    wcel
    @56
    supadd.a1
    supadd.a2
    supadd.a3
    wph
    @0
    cB
    @55
    supaddc.b
    resubcld
    vx
    vy
    va
    cA
    @49
    suprlub
    syl31anc
    adantr
    mpbid
    @52
    @50
    va
    cA
    @52
    @21
    wa
    #
    @50
    @0
    @10
    clt
    wbr
    #
    @57
    @10
    @0
    cle
    wbr
    #
    @58
    wn
    wph
    @21
    @59
    @4
    @22
    @43
    @59
    @45
    @22
    @11
    @59
    vw
    wph
    @21
    @11
    @59
    wph
    @21
    @11
    wa
    #
    wa
    #
    @8
    @59
    @60
    @8
    wph
    @60
    @12
    @8
    @11
    va
    cA
    rspe
    @20
    sylibr
    adantl
    @61
    @8
    wa
    @5
    @10
    @0
    cle
    wph
    @21
    @11
    @8
    simplrr
    wph
    @8
    @5
    @0
    cle
    wbr
    #
    @60
    wph
    @33
    @34
    @37
    w3a
    @8
    @62
    wph
    @33
    @34
    @37
    @42
    @46
    @48
    3jca
    vx
    vw
    cC
    @5
    suprub
    sylan
    adantlr
    eqbrtrrd
    mpdan
    expr
    exlimdv
    mpi
    adantlr
    @57
    @10
    @0
    wph
    @21
    @40
    @4
    @41
    adantlr
    wph
    @54
    @4
    @21
    @55
    ad2antrr
    #
    lenltd
    mpbid
    @57
    @0
    cB
    @9
    @63
    wph
    @30
    @4
    @21
    supaddc.b
    ad2antrr
    wph
    @21
    @9
    cr
    wcel
    @4
    @23
    adantlr
    ltsubaddd
    mtbird
    nrexdv
    pm2.65da
    wph
    @0
    @2
    @55
    @47
    eqleltd
    mpbir2and
    eqcomd
end
