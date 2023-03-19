include "wiso.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wn.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "wrex.mm"
include "wbr.mm"
include "wb.mm"
include "ssel.mm"
include "wf1o.mm"
include "wfn.mm"
include "wi.mm"
include "isof1o.mm"
include "f1ofn.mm"
include "fnbrfvb.mm"
include "ex.mm"
include "3syl.mm"
include "syl9r.mm"
include "imp31.mm"
include "rexbidva.mm"
include "vex.mm"
include "elima.mm"
include "syl6rbbr.mm"
include "cvv.mm"
include "fvex.mm"
include "eliniseg.mm"
include "mp1i.mm"
include "anbi12d.mm"
include "elin.mm"
include "r19.41v.mm"
include "3bitr4g.mm"
include "adantrr.mm"
include "breq1.mm"
include "biimpar.mm"
include "ad2antll.mm"
include "isorel.mm"
include "bitrd.mm"
include "syl5ibr.mm"
include "exp32.mm"
include "com34.mm"
include "imp32.mm"
include "reximdvai.mm"
include "sylbid.mm"
include "exbii.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "syl6ibr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "con4d.mm"
include "syl.mm"
include "fnfvima.mm"
include "3expia.mm"
include "sylan.mm"
include "adantrd.mm"
include "biimpd.mm"
include "ax-mp.mm"
include "impd.mm"
include "jcad.mm"
include "3imtr4g.mm"
include "n0i.mm"
include "syl6.mm"
include "impcon4bid.mm"

theorem isomin
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( H Isom R , S ( A , B ) /\ ( C C_ A /\ D e. A ) ) -> ( ( C i^i ( `' R " { D } ) ) = (/) <-> ( ( H " C ) i^i ( `' S " { ( H ` D ) } ) ) = (/) ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cC
    cA
    wss
    #
    cD
    cA
    wcel
    #
    wa
    #
    wa
    #
    cC
    cR
    ccnv
    cD
    csn
    cima
    #
    cin
    #
    c0
    wceq
    #
    cH
    cC
    cima
    #
    cS
    ccnv
    cD
    cH
    cfv
    #
    csn
    cima
    #
    cin
    #
    c0
    wceq
    #
    @4
    @12
    @7
    @12
    wn
    #
    vy
    cv
    #
    @11
    wcel
    #
    vy
    wex
    @4
    @7
    wn
    #
    vy
    @11
    neq0
    @4
    @15
    @16
    vy
    @4
    @15
    vx
    cv
    #
    @5
    wcel
    #
    vx
    cC
    wrex
    #
    @16
    @4
    @15
    @17
    cH
    cfv
    #
    @14
    wceq
    #
    @14
    @9
    cS
    wbr
    #
    wa
    #
    vx
    cC
    wrex
    #
    @19
    @0
    @1
    @15
    @24
    wb
    @2
    @0
    @1
    wa
    #
    @14
    @8
    wcel
    #
    @14
    @10
    wcel
    #
    wa
    @21
    vx
    cC
    wrex
    #
    @22
    wa
    @15
    @24
    @25
    @26
    @28
    @27
    @22
    @25
    @28
    @17
    @14
    cH
    wbr
    #
    vx
    cC
    wrex
    @26
    @25
    @21
    @29
    vx
    cC
    @0
    @1
    @17
    cC
    wcel
    #
    @21
    @29
    wb
    #
    @1
    @30
    @17
    cA
    wcel
    #
    @0
    @31
    cC
    cA
    @17
    ssel
    #
    @0
    cA
    cB
    cH
    wf1o
    #
    cH
    cA
    wfn
    #
    @32
    @31
    wi
    cA
    cB
    cR
    cS
    cH
    isof1o
    #
    cA
    cB
    cH
    f1ofn
    #
    @35
    @32
    @31
    cA
    @17
    @14
    cH
    fnbrfvb
    ex
    3syl
    syl9r
    imp31
    rexbidva
    vx
    @14
    cH
    cC
    vy
    vex
    #
    elima
    syl6rbbr
    @9
    cvv
    wcel
    #
    @27
    @22
    wb
    @25
    cD
    cH
    fvex
    #
    cS
    @9
    @14
    cvv
    @38
    eliniseg
    mp1i
    anbi12d
    @14
    @8
    @10
    elin
    @21
    @22
    vx
    cC
    r19.41v
    3bitr4g
    adantrr
    @4
    @23
    @18
    vx
    cC
    @0
    @1
    @2
    @30
    @23
    @18
    wi
    #
    wi
    @0
    @1
    @30
    @2
    @41
    @1
    @30
    @32
    @0
    @2
    @41
    wi
    @33
    @0
    @32
    @2
    @41
    @23
    @18
    @0
    @32
    @2
    wa
    wa
    #
    @20
    @9
    cS
    wbr
    #
    @21
    @43
    @22
    @20
    @14
    @9
    cS
    breq1
    biimpar
    @42
    @18
    @17
    cD
    cR
    wbr
    #
    @43
    @2
    @18
    @44
    wb
    @0
    @32
    cR
    cD
    @17
    cA
    vx
    vex
    eliniseg
    ad2antll
    #
    cA
    cB
    @17
    cD
    cR
    cS
    cH
    isorel
    #
    bitrd
    syl5ibr
    exp32
    syl9r
    com34
    imp32
    reximdvai
    sylbid
    @17
    @6
    wcel
    #
    vx
    wex
    #
    @30
    @18
    wa
    #
    vx
    wex
    @16
    @19
    @47
    @49
    vx
    @17
    cC
    @5
    elin
    #
    exbii
    vx
    @6
    neq0
    #
    @18
    vx
    cC
    df-rex
    3bitr4i
    syl6ibr
    exlimdv
    syl5bi
    con4d
    @16
    @48
    @4
    @13
    @51
    @4
    @47
    @13
    vx
    @4
    @47
    @20
    @11
    wcel
    #
    @13
    @4
    @49
    @20
    @8
    wcel
    #
    @20
    @10
    wcel
    #
    wa
    @47
    @52
    @4
    @49
    @53
    @54
    @4
    @30
    @53
    @18
    @0
    @35
    @3
    @30
    @53
    wi
    #
    @0
    @34
    @35
    @36
    @37
    syl
    @35
    @1
    @55
    @2
    @35
    @1
    @30
    @53
    cA
    cC
    cH
    @17
    fnfvima
    3expia
    adantrr
    sylan
    adantrd
    @4
    @30
    @18
    @54
    @0
    @1
    @2
    @30
    @18
    @54
    wi
    #
    wi
    @0
    @1
    @30
    @2
    @56
    @1
    @30
    @32
    @0
    @2
    @56
    wi
    @33
    @0
    @32
    @2
    @56
    @42
    @18
    @44
    @54
    @45
    @42
    @44
    @43
    @54
    @42
    @44
    @43
    @46
    biimpd
    @39
    @54
    @43
    wb
    @40
    cS
    @9
    @20
    cvv
    @17
    cH
    fvex
    eliniseg
    ax-mp
    syl6ibr
    sylbid
    exp32
    syl9r
    com34
    imp32
    impd
    jcad
    @50
    @20
    @8
    @10
    elin
    3imtr4g
    @11
    @20
    n0i
    syl6
    exlimdv
    syl5bi
    impcon4bid
end
