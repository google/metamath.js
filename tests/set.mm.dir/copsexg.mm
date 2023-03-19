include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "vex.mm"
include "eqvinop.mm"
include "19.8a.mm"
include "19.23bi.mm"
include "ex.mm"
include "weq.mm"
include "opth.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "nfe1.mm"
include "wal.mm"
include "anim2i.mm"
include "anassrs.mm"
include "eximi.mm"
include "biidd.mm"
include "drex1.mm"
include "syl5ib.mm"
include "wn.mm"
include "anass.mm"
include "exbii.mm"
include "19.40.mm"
include "nfeqf2.mm"
include "19.9d.mm"
include "anim1d.mm"
include "syl5.mm"
include "syl5bi.mm"
include "syl6.mm"
include "pm2.61i.mm"
include "exlimi.mm"
include "weu.mm"
include "euequ1.mm"
include "equcom.mm"
include "eubii.mm"
include "mpbi.mm"
include "eupick.mm"
include "mpan.mm"
include "com12.mm"
include "sylan9.mm"
include "sylbi.mm"
include "impbid.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2exbidv.mm"
include "bibi2d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimivv.mm"
include "pm2.43i.mm"

theorem copsexg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint y z
  disjoint w y
  disjoint ph z
  disjoint ph w
  assert |- ( A = <. x , y >. -> ( ph <-> E. x E. y ( A = <. x , y >. /\ ph ) ) )

  proof
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    @3
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    wb
    #
    @3
    cA
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    @9
    @2
    wceq
    #
    wa
    #
    vw
    wex
    vz
    wex
    @3
    @6
    wi
    #
    vz
    vw
    cA
    @0
    @1
    vx
    vex
    vy
    vex
    eqvinop
    @12
    @13
    vz
    vw
    @10
    @13
    @11
    @10
    @13
    @11
    wph
    @11
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wb
    #
    wi
    @11
    wph
    @16
    @11
    wph
    @16
    @14
    @16
    vy
    @15
    vx
    19.8a
    19.23bi
    ex
    @11
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    @16
    wph
    wi
    @7
    @8
    @0
    @1
    vz
    vex
    vw
    vex
    opth
    #
    @16
    @20
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @20
    wph
    @14
    @22
    vx
    vy
    @11
    @20
    wph
    @21
    anbi1i
    2exbii
    @24
    @18
    @19
    wph
    wa
    #
    vy
    wex
    #
    wa
    #
    vx
    wex
    #
    @20
    wph
    @23
    @28
    vx
    @27
    vx
    nfe1
    vy
    vx
    weq
    vy
    wal
    #
    @23
    @28
    wi
    @23
    @27
    vy
    wex
    @29
    @28
    @22
    @27
    vy
    @18
    @19
    wph
    @27
    @25
    @26
    @18
    @25
    vy
    19.8a
    anim2i
    anassrs
    eximi
    @27
    @27
    vy
    vx
    @29
    @27
    biidd
    drex1
    syl5ib
    @29
    wn
    #
    @23
    @27
    @28
    @23
    @18
    @25
    wa
    #
    vy
    wex
    #
    @30
    @27
    @22
    @31
    vy
    @18
    @19
    wph
    anass
    exbii
    @32
    @18
    vy
    wex
    #
    @26
    wa
    @30
    @27
    @18
    @25
    vy
    19.40
    @30
    @33
    @18
    @26
    @18
    @30
    vy
    vy
    vx
    vz
    nfeqf2
    19.9d
    anim1d
    syl5
    syl5bi
    @27
    vx
    19.8a
    syl6
    pm2.61i
    exlimi
    @18
    @28
    @26
    @19
    wph
    @28
    @18
    @26
    @18
    vx
    weu
    #
    @28
    @18
    @26
    wi
    vx
    vz
    weq
    #
    vx
    weu
    @34
    vx
    vz
    euequ1
    @35
    @18
    vx
    vx
    vz
    equcom
    eubii
    mpbi
    @18
    @26
    vx
    eupick
    mpan
    com12
    @26
    @19
    wph
    @19
    vy
    weu
    #
    @26
    @19
    wph
    wi
    vy
    vw
    weq
    #
    vy
    weu
    @36
    vy
    vw
    euequ1
    @37
    @19
    vy
    vy
    vw
    equcom
    eubii
    mpbi
    @19
    wph
    vy
    eupick
    mpan
    com12
    sylan9
    syl5
    syl5bi
    sylbi
    impbid
    @10
    @3
    @11
    @6
    @17
    cA
    @9
    @2
    eqeq1
    #
    @10
    @5
    @16
    wph
    @10
    @4
    @14
    vx
    vy
    @10
    @3
    @11
    wph
    @38
    anbi1d
    2exbidv
    bibi2d
    imbi12d
    mpbiri
    adantr
    exlimivv
    sylbi
    pm2.43i
end
