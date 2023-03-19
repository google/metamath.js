include "ccat.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cful.mm"
include "co.mm"
include "cfth.mm"
include "cin.mm"
include "cfunc.mm"
include "wrel.mm"
include "wceq.mm"
include "relfunc.mm"
include "idfucl.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "wf1o.mm"
include "cbs.mm"
include "wral.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "sylibr.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "f1oi.mm"
include "eqid.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "idfu2nd.mm"
include "eqidd.mm"
include "idfu1.mm"
include "oveq12d.mm"
include "f1oeq123d.mm"
include "mpbiri.mm"
include "ralrimivva.mm"
include "isffth2.mm"
include "sylanbrc.mm"
include "sylib.mm"
include "eqeltrd.mm"

theorem idffth
  let cC: class C
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume idffth.i: |- I = ( idFunc ` C )


  assert |- ( C e. Cat -> I e. ( ( C Full C ) i^i ( C Faith C ) ) )

  proof
    cC
    ccat
    wcel
    #
    cI
    cI
    c1st
    cfv
    #
    cI
    c2nd
    cfv
    #
    cop
    #
    cC
    cC
    cful
    co
    cC
    cC
    cfth
    co
    cin
    #
    @0
    cC
    cC
    cfunc
    co
    #
    wrel
    cI
    @5
    wcel
    cI
    @3
    wceq
    cC
    cC
    relfunc
    cC
    cI
    idffth.i
    idfucl
    #
    cI
    @5
    1st2nd
    sylancr
    #
    @0
    @1
    @2
    @4
    wbr
    #
    @3
    @4
    wcel
    @0
    @1
    @2
    @5
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @10
    @1
    cfv
    #
    @11
    @1
    cfv
    #
    @12
    co
    #
    @10
    @11
    @2
    co
    #
    wf1o
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    vx
    @19
    wral
    @8
    @0
    @3
    @5
    wcel
    @9
    @0
    cI
    @3
    @5
    @7
    @6
    eqeltrrd
    @1
    @2
    @5
    df-br
    sylibr
    @0
    @18
    vx
    vy
    @19
    @19
    @0
    @10
    @19
    wcel
    #
    @11
    @19
    wcel
    #
    wa
    #
    wa
    #
    @18
    @13
    @13
    cid
    @13
    cres
    #
    wf1o
    @13
    f1oi
    @23
    @13
    @13
    @16
    @13
    @17
    @24
    @23
    @19
    cC
    @12
    cI
    @10
    @11
    idffth.i
    @19
    eqid
    #
    @0
    @22
    simpl
    #
    @12
    eqid
    #
    @0
    @20
    @21
    simprl
    #
    @0
    @20
    @21
    simprr
    #
    idfu2nd
    @23
    @13
    eqidd
    @23
    @14
    @10
    @15
    @11
    @12
    @23
    @19
    cC
    cI
    @10
    idffth.i
    @25
    @26
    @28
    idfu1
    @23
    @19
    cC
    cI
    @11
    idffth.i
    @25
    @26
    @29
    idfu1
    oveq12d
    f1oeq123d
    mpbiri
    ralrimivva
    vx
    vy
    @19
    cC
    cC
    @1
    @2
    @12
    @12
    @25
    @27
    @27
    isffth2
    sylanbrc
    @1
    @2
    @4
    df-br
    sylib
    eqeltrd
end
