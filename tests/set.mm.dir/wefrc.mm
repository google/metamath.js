include "cep.mm"
include "wwe.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wess.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "adantl.mm"
include "wel.mm"
include "inss1.mm"
include "wfr.mm"
include "wefr.mm"
include "vex.mm"
include "inex2.mm"
include "epfrc.mm"
include "syl3an1.mm"
include "3exp.mm"
include "mpi.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "rexbii2.mm"
include "syl6ib.mm"
include "adantr.mm"
include "wral.mm"
include "w3a.mm"
include "df-3an.mm"
include "3anrot.mm"
include "bitr3i.mm"
include "wetrep.mm"
include "expd.mm"
include "sylan2b.mm"
include "exp44.mm"
include "imp.mm"
include "com34.mm"
include "impd.mm"
include "syl5bi.mm"
include "imp4a.mm"
include "com23.mm"
include "ralrimdv.mm"
include "dfss3.mm"
include "syl6ibr.mm"
include "dfss.mm"
include "in32.mm"
include "eqeq2i.mm"
include "sylbb.mm"
include "biimprd.mm"
include "syl6.mm"
include "reximdvai.mm"
include "syld.mm"
include "pm2.61dne.mm"
include "exlimdv.mm"
include "syl6com.mm"
include "3imp.mm"

theorem wefrc
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint B x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint B y
  disjoint B z
  assert |- ( ( _E We A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) )

  proof
    cA
    cep
    wwe
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    cB
    vx
    cv
    #
    cin
    #
    c0
    wceq
    #
    vx
    cB
    wrex
    #
    @1
    @0
    cB
    cep
    wwe
    #
    @2
    @6
    wi
    cB
    cA
    cep
    wess
    @2
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    @7
    @6
    vy
    cB
    n0
    @7
    @9
    @6
    vy
    @7
    @9
    @6
    @7
    @9
    wa
    #
    @6
    cB
    @8
    cin
    #
    c0
    @9
    @11
    c0
    wceq
    #
    @6
    wi
    @7
    @9
    @12
    @6
    @5
    @12
    vx
    @8
    cB
    @3
    @8
    wceq
    @4
    @11
    c0
    @3
    @8
    cB
    ineq2
    eqeq1d
    rspcev
    ex
    adantl
    @10
    @11
    c0
    wne
    #
    vx
    vy
    wel
    #
    @11
    @3
    cin
    #
    c0
    wceq
    #
    wa
    #
    vx
    cB
    wrex
    #
    @6
    @7
    @13
    @18
    wi
    @9
    @7
    @13
    @16
    vx
    @11
    wrex
    #
    @18
    @7
    @11
    cB
    wss
    #
    @13
    @19
    wi
    cB
    @8
    inss1
    @7
    @20
    @13
    @19
    @7
    cB
    cep
    wfr
    @20
    @13
    @19
    cB
    cep
    wefr
    vx
    cB
    @11
    @8
    cB
    vy
    vex
    inex2
    epfrc
    syl3an1
    3exp
    mpi
    @16
    @17
    vx
    @11
    cB
    @3
    @11
    wcel
    #
    @16
    wa
    @3
    cB
    wcel
    #
    @14
    wa
    #
    @16
    wa
    @22
    @17
    wa
    @21
    @23
    @16
    @3
    cB
    @8
    elin
    anbi1i
    @22
    @14
    @16
    anass
    bitri
    rexbii2
    syl6ib
    adantr
    @10
    @17
    @5
    vx
    cB
    @10
    @22
    @14
    @16
    @5
    @10
    @22
    @14
    @16
    @5
    wi
    #
    @10
    @23
    @4
    @8
    wss
    #
    @24
    @10
    @23
    vz
    vy
    wel
    #
    vz
    @4
    wral
    @25
    @10
    @23
    @26
    vz
    @4
    @10
    vz
    cv
    #
    @4
    wcel
    #
    @23
    @26
    @10
    @28
    @22
    @14
    @26
    @28
    @27
    cB
    wcel
    #
    vz
    vx
    wel
    #
    wa
    @10
    @22
    @14
    @26
    wi
    #
    wi
    #
    @27
    cB
    @3
    elin
    @10
    @29
    @30
    @32
    @10
    @29
    @22
    @30
    @31
    @7
    @9
    @29
    @22
    @30
    @31
    wi
    #
    wi
    wi
    @7
    @9
    @29
    @22
    @33
    @9
    @29
    wa
    @22
    wa
    #
    @7
    @29
    @22
    @9
    w3a
    #
    @33
    @34
    @9
    @29
    @22
    w3a
    @35
    @9
    @29
    @22
    df-3an
    @9
    @29
    @22
    3anrot
    bitr3i
    @7
    @35
    wa
    @30
    @14
    @26
    vz
    vx
    vy
    cB
    wetrep
    expd
    sylan2b
    exp44
    imp
    com34
    impd
    syl5bi
    imp4a
    com23
    ralrimdv
    vz
    @4
    @8
    dfss3
    syl6ibr
    @25
    @5
    @16
    @25
    @4
    @15
    c0
    @25
    @4
    @4
    @8
    cin
    #
    wceq
    @4
    @15
    wceq
    @4
    @8
    dfss
    @36
    @15
    @4
    cB
    @3
    @8
    in32
    eqeq2i
    sylbb
    eqeq1d
    biimprd
    syl6
    expd
    imp4a
    reximdvai
    syld
    pm2.61dne
    ex
    exlimdv
    syl5bi
    syl6com
    3imp
end
