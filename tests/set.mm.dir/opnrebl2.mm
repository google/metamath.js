include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wa.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cabs.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "eqid.mm"
include "rexmet.mm"
include "cmopn.mm"
include "tgioo.mm"
include "mopnss.mm"
include "mpan.mm"
include "clt.mm"
include "cbl.mm"
include "wi.mm"
include "w3a.mm"
include "mopni3.mm"
include "ex.mm"
include "mp3an1.mm"
include "sselda.mm"
include "wceq.mm"
include "rpre.mm"
include "bl2ioo.mm"
include "sylan2.mm"
include "sseq1d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "biimpd.mm"
include "ltle.mm"
include "syl2anr.mm"
include "anim1d.mm"
include "reximdva.mm"
include "syl9.mm"
include "syl.mm"
include "mpdd.mm"
include "expimpd.mm"
include "ralrimivv.mm"
include "jca.mm"
include "ssel2.mm"
include "c1.mm"
include "1rp.mm"
include "simpr.mm"
include "reximi.mm"
include "ralimi.mm"
include "biidd.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "imdistani.mm"
include "wb.mm"
include "elmopn2.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "impbii.mm"

theorem opnrebl2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. ( topGen ` ran (,) ) <-> ( A C_ RR /\ A. x e. A A. y e. RR+ E. z e. RR+ ( z <_ y /\ ( ( x - z ) (,) ( x + z ) ) C_ A ) ) )

  proof
    cA
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    cA
    cr
    wss
    #
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cv
    #
    @3
    cmin
    co
    @6
    @3
    caddc
    co
    cioo
    co
    #
    cA
    wss
    #
    wa
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    @1
    @2
    @12
    cabs
    cmin
    ccom
    cr
    cr
    cxp
    cres
    #
    cr
    cxmt
    cfv
    wcel
    #
    @1
    @2
    @14
    @14
    eqid
    #
    rexmet
    #
    cA
    @14
    @0
    cr
    @14
    @14
    cmopn
    cfv
    #
    @16
    @18
    eqid
    tgioo
    #
    mopnss
    mpan
    #
    @1
    @10
    vx
    vy
    cA
    crp
    @1
    @6
    cA
    wcel
    #
    @4
    crp
    wcel
    #
    @10
    @1
    @21
    wa
    #
    @22
    @3
    @4
    clt
    wbr
    #
    @6
    @3
    @14
    cbl
    cfv
    co
    #
    cA
    wss
    #
    wa
    #
    vz
    crp
    wrex
    #
    @10
    @15
    @1
    @21
    @22
    @28
    wi
    @17
    @15
    @1
    @21
    w3a
    @22
    @28
    vz
    cA
    @14
    @6
    @4
    @0
    cr
    @19
    mopni3
    ex
    mp3an1
    @23
    @6
    cr
    wcel
    #
    @22
    @28
    @10
    wi
    wi
    @1
    cA
    cr
    @6
    @20
    sselda
    @29
    @28
    @24
    @8
    wa
    #
    vz
    crp
    wrex
    #
    @22
    @10
    @29
    @28
    @31
    @29
    @27
    @30
    vz
    crp
    @29
    @3
    crp
    wcel
    #
    wa
    #
    @26
    @8
    @24
    @33
    @25
    @7
    cA
    @32
    @29
    @3
    cr
    wcel
    #
    @25
    @7
    wceq
    @3
    rpre
    #
    @6
    @3
    @14
    @16
    bl2ioo
    sylan2
    sseq1d
    #
    anbi2d
    rexbidva
    biimpd
    @22
    @30
    @9
    vz
    crp
    @22
    @32
    wa
    @24
    @5
    @8
    @32
    @34
    @4
    cr
    wcel
    @24
    @5
    wi
    @22
    @35
    @4
    rpre
    @3
    @4
    ltle
    syl2anr
    anim1d
    reximdva
    syl9
    syl
    mpdd
    expimpd
    ralrimivv
    jca
    @13
    @2
    @26
    vz
    crp
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    @1
    @2
    @12
    @38
    @2
    @11
    @37
    vx
    cA
    @2
    @21
    wa
    @29
    @11
    @37
    wi
    cA
    cr
    @6
    ssel2
    @11
    @37
    @29
    @8
    vz
    crp
    wrex
    #
    c1
    crp
    wcel
    @11
    @40
    vy
    crp
    wral
    @40
    1rp
    @10
    @40
    vy
    crp
    @9
    @8
    vz
    crp
    @5
    @8
    simpr
    reximi
    ralimi
    @40
    @40
    vy
    c1
    crp
    @4
    c1
    wceq
    @40
    biidd
    rspcv
    mpsyl
    @29
    @26
    @8
    vz
    crp
    @36
    rexbidva
    syl5ibr
    syl
    ralimdva
    imdistani
    @15
    @1
    @39
    wb
    @17
    vx
    vz
    cA
    @14
    @0
    cr
    @19
    elmopn2
    ax-mp
    sylibr
    impbii
end
