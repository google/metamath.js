include "c0.mm"
include "wne.mm"
include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "csn.mm"
include "wss.mm"
include "wtr.mm"
include "wa.mm"
include "wal.mm"
include "w3a.mm"
include "snssi.mm"
include "anim2i.mm"
include "ssin.mm"
include "vex.mm"
include "snss.mm"
include "bitr4i.mm"
include "sylib.mm"
include "ne0i.mm"
include "syl.mm"
include "inss2.mm"
include "inex1.mm"
include "epfrc.mm"
include "mp3an2.mm"
include "wel.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "inss1.mm"
include "sseli.mm"
include "ancri.mm"
include "trel.mm"
include "inass.mm"
include "incom.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "bitr2i.mm"
include "sylbi.mm"
include "ex.mm"
include "syl6.mm"
include "expd.mm"
include "com34.mm"
include "impd.mm"
include "syl5.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "com23.mm"
include "imp.mm"
include "necon4d.mm"
include "anim2d.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "expcomd.mm"
include "impcom.mm"
include "3adant3.mm"
include "snex.mm"
include "tz9.1.mm"
include "exlimiiv.mm"
include "exlimiv.mm"

theorem epfrs
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( ( _E Fr A /\ A =/= (/) ) -> E. x e. A ( x i^i A ) = (/) )

  proof
    cA
    c0
    wne
    #
    cA
    cep
    wfr
    #
    vx
    cv
    #
    cA
    cin
    #
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    vz
    cv
    #
    cA
    wcel
    #
    vz
    wex
    @1
    @5
    wi
    #
    vz
    cA
    n0
    @7
    @8
    vz
    @6
    csn
    #
    vy
    cv
    #
    wss
    #
    @10
    wtr
    #
    @9
    vw
    cv
    #
    wss
    @13
    wtr
    wa
    @10
    @13
    wss
    wi
    vw
    wal
    #
    w3a
    @7
    @8
    wi
    #
    vy
    @11
    @12
    @15
    @14
    @12
    @11
    @15
    @12
    @11
    @7
    @8
    @11
    @7
    wa
    #
    @10
    cA
    cin
    #
    c0
    wne
    #
    @12
    @8
    @16
    @6
    @17
    wcel
    #
    @18
    @16
    @11
    @9
    cA
    wss
    #
    wa
    #
    @19
    @7
    @20
    @11
    @6
    cA
    snssi
    anim2i
    @21
    @9
    @17
    wss
    @19
    @9
    @10
    cA
    ssin
    @6
    @17
    vz
    vex
    snss
    bitr4i
    sylib
    @17
    @6
    ne0i
    syl
    @12
    @1
    @18
    @5
    @1
    @18
    wa
    @17
    @2
    cin
    #
    c0
    wceq
    #
    vx
    @17
    wrex
    #
    @12
    @5
    @1
    @17
    cA
    wss
    @18
    @24
    @10
    cA
    inss2
    vx
    cA
    @17
    @10
    cA
    vy
    vex
    inex1
    epfrc
    mp3an2
    @12
    @23
    @4
    vx
    @17
    cA
    @2
    @17
    wcel
    #
    @23
    wa
    #
    vx
    vy
    wel
    #
    @2
    cA
    wcel
    #
    @23
    wa
    #
    wa
    #
    @12
    @28
    @4
    wa
    #
    @26
    @27
    @28
    wa
    #
    @23
    wa
    @30
    @25
    @32
    @23
    @2
    @10
    cA
    elin
    anbi1i
    @27
    @28
    @23
    anass
    bitri
    @12
    @27
    @29
    @31
    @12
    @27
    wa
    #
    @23
    @4
    @28
    @33
    @3
    c0
    @22
    c0
    @12
    @27
    @3
    c0
    wne
    #
    @22
    c0
    wne
    #
    wi
    @12
    @34
    @27
    @35
    @34
    @13
    @3
    wcel
    #
    vw
    wex
    @12
    @27
    @35
    wi
    #
    vw
    @3
    n0
    @12
    @36
    @37
    vw
    @36
    vw
    vx
    wel
    #
    @36
    wa
    @12
    @37
    @36
    @38
    @3
    @2
    @13
    @2
    cA
    inss1
    sseli
    ancri
    @12
    @38
    @36
    @37
    @12
    @38
    @27
    @36
    @35
    @12
    @38
    @27
    @36
    @35
    wi
    #
    @12
    @38
    @27
    wa
    vw
    vy
    wel
    #
    @39
    @10
    @13
    @2
    trel
    @40
    @36
    @35
    @40
    @36
    wa
    #
    @13
    @22
    wcel
    #
    @35
    @42
    @13
    @10
    @3
    cin
    #
    wcel
    @41
    @22
    @43
    @13
    @22
    @10
    cA
    @2
    cin
    #
    cin
    @43
    @10
    cA
    @2
    inass
    @44
    @3
    @10
    cA
    @2
    incom
    ineq2i
    eqtri
    eleq2i
    @13
    @10
    @3
    elin
    bitr2i
    @22
    @13
    ne0i
    sylbi
    ex
    syl6
    expd
    com34
    impd
    syl5
    exlimdv
    syl5bi
    com23
    imp
    necon4d
    anim2d
    expimpd
    syl5bi
    reximdv2
    syl5
    expcomd
    syl5
    expd
    impcom
    3adant3
    vy
    vw
    @9
    @6
    snex
    tz9.1
    exlimiiv
    exlimiv
    sylbi
    impcom
end
