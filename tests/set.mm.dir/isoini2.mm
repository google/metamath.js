include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "cima.mm"
include "wf1.mm"
include "wss.mm"
include "isof1o.mm"
include "f1of1.mm"
include "syl.mm"
include "adantr.mm"
include "ccnv.mm"
include "csn.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstri.mm"
include "f1ores.mm"
include "sylancl.mm"
include "wceq.mm"
include "isoini.mm"
include "imaeq2i.mm"
include "3eqtr4g.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "df-isom.mm"
include "simprbi.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "mpsyl.mm"
include "fvres.mm"
include "breqan12d.mm"
include "bibi2d.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "sylanbrc.mm"

theorem isoini2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume isoini2.1: |- C = ( A i^i ( `' R " { X } ) )
  assume isoini2.2: |- D = ( B i^i ( `' S " { ( H ` X ) } ) )


  assert |- ( ( H Isom R , S ( A , B ) /\ X e. A ) -> ( H |` C ) Isom R , S ( C , D ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cX
    cA
    wcel
    #
    wa
    #
    cC
    cD
    cH
    cC
    cres
    #
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @5
    @3
    cfv
    #
    @6
    @3
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cC
    wral
    #
    vx
    cC
    wral
    #
    cC
    cD
    cR
    cS
    @3
    wiso
    @2
    cC
    cH
    cC
    cima
    #
    @3
    wf1o
    #
    @4
    @2
    cA
    cB
    cH
    wf1
    #
    cC
    cA
    wss
    #
    @15
    @0
    @16
    @1
    @0
    cA
    cB
    cH
    wf1o
    #
    @16
    cA
    cB
    cR
    cS
    cH
    isof1o
    cA
    cB
    cH
    f1of1
    syl
    adantr
    cC
    cA
    cR
    ccnv
    cX
    csn
    cima
    #
    cin
    #
    cA
    isoini2.1
    cA
    @19
    inss1
    eqsstri
    #
    cA
    cB
    cC
    cH
    f1ores
    sylancl
    @2
    @14
    cD
    wceq
    @15
    @4
    wb
    @2
    cH
    @20
    cima
    cB
    cS
    ccnv
    cX
    cH
    cfv
    csn
    cima
    cin
    @14
    cD
    cA
    cB
    cX
    cR
    cS
    cH
    isoini
    cC
    @20
    cH
    isoini2.1
    imaeq2i
    isoini2.2
    3eqtr4g
    @14
    cD
    cC
    @3
    f1oeq3
    syl
    mpbid
    @2
    @7
    @5
    cH
    cfv
    #
    @6
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    cC
    wral
    #
    vx
    cC
    wral
    #
    @13
    @17
    @2
    @26
    vx
    cA
    wral
    #
    @27
    @21
    @17
    @2
    @25
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @28
    @21
    @0
    @30
    @1
    @0
    @18
    @30
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    df-isom
    simprbi
    adantr
    @17
    @29
    @26
    vx
    cA
    @25
    vy
    cC
    cA
    ssralv
    ralimdv
    mpsyl
    @26
    vx
    cC
    cA
    ssralv
    mpsyl
    @12
    @26
    vx
    cC
    @5
    cC
    wcel
    #
    @11
    @25
    vy
    cC
    @31
    @6
    cC
    wcel
    #
    wa
    @10
    @24
    @7
    @31
    @32
    @8
    @22
    @9
    @23
    cS
    @5
    cC
    cH
    fvres
    @6
    cC
    cH
    fvres
    breqan12d
    bibi2d
    ralbidva
    ralbiia
    sylibr
    vx
    vy
    cC
    cD
    cR
    cS
    @3
    df-isom
    sylanbrc
end
