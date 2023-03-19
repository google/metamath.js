include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cec.mm"
include "wceq.mm"
include "co.mm"
include "wb.mm"
include "cxp.mm"
include "opelxpi.mm"
include "ad2antrr.mm"
include "wer.mm"
include "a1i.mm"
include "simpr.mm"
include "ereldm.mm"
include "mpbid.mm"
include "opelxp2.mm"
include "syl.mm"
include "ex.mm"
include "wi.mm"
include "caovcl.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "ndmovrcl.mm"
include "simprd.mm"
include "syl6com.mm"
include "adantll.mm"
include "wbr.mm"
include "adantr.mm"
include "erth.mm"
include "bitr3d.mm"
include "expr.mm"
include "pm5.21ndd.mm"
include "an32s.mm"
include "wn.mm"
include "c0.mm"
include "eqcom.mm"
include "wne.mm"
include "cdm.mm"
include "erdm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "ecdmn0.mm"
include "opelxp.mm"
include "3bitr3i.mm"
include "simplbi2.mm"
include "ad2antlr.mm"
include "necon2bd.mm"
include "con3i.mm"
include "ndmov.mm"
include "syl6.mm"
include "mtbiri.mm"
include "simprbi.mm"
include "syl5.mm"
include "necon1bd.mm"
include "impbid.mm"
include "syl5bb.mm"
include "necon1bi.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "simpl.mm"
include "eqeq2d.mm"
include "3bitr4d.mm"
include "pm2.61dan.mm"

theorem eceqoveq
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  assume eceqoveq.5: |- .~ Er ( S X. S )
  assume eceqoveq.7: |- dom .+ = ( S X. S )
  assume eceqoveq.8: |- -. (/) e. S
  assume eceqoveq.9: |- ( ( x e. S /\ y e. S ) -> ( x .+ y ) e. S )
  assume eceqoveq.10: |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( <. A , B >. .~ <. C , D >. <-> ( A .+ D ) = ( B .+ C ) ) )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A e. S /\ C e. S ) -> ( [ <. A , B >. ] .~ = [ <. C , D >. ] .~ <-> ( A .+ D ) = ( B .+ C ) ) )

  proof
    cA
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    wa
    #
    cB
    cS
    wcel
    #
    cA
    cB
    cop
    #
    c.sm
    cec
    #
    cC
    cD
    cop
    #
    c.sm
    cec
    #
    wceq
    #
    cA
    cD
    c.pl
    co
    #
    cB
    cC
    c.pl
    co
    #
    wceq
    #
    wb
    #
    @0
    @3
    @1
    @12
    @0
    @3
    wa
    #
    @1
    wa
    #
    cD
    cS
    wcel
    #
    @8
    @11
    @14
    @8
    @15
    @14
    @8
    wa
    #
    @6
    cS
    cS
    cxp
    #
    wcel
    #
    @15
    @16
    @4
    @17
    wcel
    #
    @18
    @13
    @19
    @1
    @8
    cA
    cB
    cS
    cS
    opelxpi
    #
    ad2antrr
    @16
    @4
    @6
    c.sm
    @17
    @17
    c.sm
    wer
    #
    @16
    eceqoveq.5
    a1i
    @14
    @8
    simpr
    ereldm
    mpbid
    cC
    cD
    cS
    cS
    opelxp2
    syl
    ex
    @3
    @1
    @11
    @15
    wi
    @0
    @11
    @3
    @1
    wa
    #
    @9
    cS
    wcel
    #
    @15
    @22
    @23
    @11
    @10
    cS
    wcel
    vx
    vy
    cB
    cC
    cS
    c.pl
    eceqoveq.9
    caovcl
    @9
    @10
    cS
    eleq1
    syl5ibr
    @23
    @0
    @15
    cA
    cD
    cS
    c.pl
    eceqoveq.7
    eceqoveq.8
    ndmovrcl
    simprd
    syl6com
    adantll
    @13
    @1
    @15
    @12
    @13
    @1
    @15
    wa
    #
    wa
    #
    @4
    @6
    c.sm
    wbr
    @8
    @11
    @25
    @4
    @6
    c.sm
    @17
    @21
    @25
    eceqoveq.5
    a1i
    @13
    @19
    @24
    @20
    adantr
    erth
    eceqoveq.10
    bitr3d
    expr
    pm5.21ndd
    an32s
    @2
    @3
    wn
    #
    wa
    #
    c0
    @7
    wceq
    #
    @9
    c0
    wceq
    #
    @8
    @11
    @28
    @7
    c0
    wceq
    #
    @27
    @29
    c0
    @7
    eqcom
    @27
    @30
    @29
    @27
    @30
    @15
    wn
    #
    @29
    @27
    @15
    @7
    c0
    @1
    @15
    @7
    c0
    wne
    #
    wi
    @0
    @26
    @32
    @1
    @15
    @6
    c.sm
    cdm
    #
    wcel
    @18
    @32
    @24
    @33
    @17
    @6
    @21
    @33
    @17
    wceq
    eceqoveq.5
    @17
    c.sm
    erdm
    ax-mp
    #
    eleq2i
    @6
    c.sm
    ecdmn0
    cC
    cD
    cS
    cS
    opelxp
    3bitr3i
    #
    simplbi2
    ad2antlr
    necon2bd
    @31
    @0
    @15
    wa
    #
    wn
    @29
    @36
    @15
    @0
    @15
    simpr
    con3i
    cA
    cD
    cS
    c.pl
    eceqoveq.7
    ndmov
    syl
    syl6
    @29
    @23
    wn
    @27
    @30
    @29
    @23
    c0
    cS
    wcel
    eceqoveq.8
    @9
    c0
    cS
    eleq1
    mtbiri
    @27
    @23
    @7
    c0
    @32
    @15
    @27
    @23
    @32
    @1
    @15
    @35
    simprbi
    @0
    @15
    @23
    wi
    @1
    @26
    @0
    @15
    @23
    vx
    vy
    cA
    cD
    cS
    c.pl
    eceqoveq.9
    caovcl
    ex
    ad2antrr
    syl5
    necon1bd
    syl5
    impbid
    syl5bb
    @27
    @5
    c0
    @7
    @26
    @5
    c0
    wceq
    @2
    @3
    @5
    c0
    @5
    c0
    wne
    #
    @0
    @3
    @4
    @33
    wcel
    @19
    @37
    @13
    @33
    @17
    @4
    @34
    eleq2i
    @4
    c.sm
    ecdmn0
    cA
    cB
    cS
    cS
    opelxp
    3bitr3i
    simprbi
    necon1bi
    adantl
    eqeq1d
    @27
    @10
    c0
    @9
    @26
    @10
    c0
    wceq
    #
    @2
    @26
    @22
    wn
    @38
    @22
    @3
    @3
    @1
    simpl
    con3i
    cB
    cC
    cS
    c.pl
    eceqoveq.7
    ndmov
    syl
    adantl
    eqeq2d
    3bitr4d
    pm2.61dan
end
