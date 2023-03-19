include "crecs.mm"
include "con0.mm"
include "cep.mm"
include "cwrecs.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "cuni.mm"
include "wrex.mm"
include "df-recs.mm"
include "df-wrecs.mm"
include "wcel.mm"
include "3anass.mm"
include "word.mm"
include "wtr.mm"
include "vex.mm"
include "elon.mm"
include "ordsson.mm"
include "ordtr.mm"
include "jca.mm"
include "wwe.mm"
include "epweon.mm"
include "wess.mm"
include "mpi.mm"
include "anim2i.mm"
include "ancoms.mm"
include "df-ord.mm"
include "sylibr.mm"
include "impbii.mm"
include "wel.mm"
include "wb.mm"
include "ssel2.mm"
include "predon.mm"
include "sseq1d.mm"
include "syl.mm"
include "ralbidva.mm"
include "dftr3.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "onelon.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "an12.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "abbii.mm"
include "unieqi.mm"
include "3eqtri.mm"

theorem dfrecs3
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F

  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f x
  disjoint f y
  disjoint x y
  assert |- recs ( F ) = U. { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  proof
    cF
    crecs
    con0
    cep
    cF
    cwrecs
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    @1
    con0
    wss
    #
    con0
    cep
    vy
    cv
    #
    cpred
    #
    @1
    wss
    #
    vy
    @1
    wral
    #
    wa
    #
    @4
    @0
    cfv
    #
    @0
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @1
    wral
    #
    w3a
    #
    vx
    wex
    #
    vf
    cab
    #
    cuni
    @2
    @9
    @0
    @4
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @1
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    cF
    df-recs
    vx
    vy
    con0
    cep
    vf
    cF
    df-wrecs
    @16
    @23
    @15
    @22
    vf
    @15
    @1
    con0
    wcel
    #
    @21
    wa
    #
    vx
    wex
    @22
    @14
    @25
    vx
    @14
    @2
    @8
    @13
    wa
    #
    wa
    @2
    @24
    @20
    wa
    #
    wa
    @25
    @2
    @8
    @13
    3anass
    @26
    @27
    @2
    @26
    @24
    @13
    wa
    @27
    @24
    @8
    @13
    @24
    @1
    word
    #
    @3
    @1
    wtr
    #
    wa
    #
    @8
    @1
    vx
    vex
    elon
    @28
    @30
    @28
    @3
    @29
    @1
    ordsson
    @1
    ordtr
    jca
    @30
    @29
    @1
    cep
    wwe
    #
    wa
    #
    @28
    @29
    @3
    @32
    @3
    @31
    @29
    @3
    con0
    cep
    wwe
    @31
    epweon
    @1
    con0
    cep
    wess
    mpi
    anim2i
    ancoms
    @1
    df-ord
    sylibr
    impbii
    @3
    @29
    @7
    @3
    @7
    @4
    @1
    wss
    #
    vy
    @1
    wral
    @29
    @3
    @6
    @33
    vy
    @1
    @3
    vy
    vx
    wel
    #
    wa
    @4
    con0
    wcel
    #
    @6
    @33
    wb
    @1
    con0
    @4
    ssel2
    @35
    @5
    @4
    @1
    @4
    predon
    #
    sseq1d
    syl
    ralbidva
    vy
    @1
    dftr3
    syl6rbbr
    pm5.32i
    3bitri
    anbi1i
    @24
    @13
    @20
    @24
    @12
    @19
    vy
    @1
    @24
    @34
    wa
    @35
    @12
    @19
    wb
    @1
    @4
    onelon
    @35
    @11
    @18
    @9
    @35
    @10
    @17
    cF
    @35
    @5
    @4
    @0
    @36
    reseq2d
    fveq2d
    eqeq2d
    syl
    ralbidva
    pm5.32i
    bitr3i
    anbi2i
    @2
    @24
    @20
    an12
    3bitri
    exbii
    @21
    vx
    con0
    df-rex
    bitr4i
    abbii
    unieqi
    3eqtri
end
