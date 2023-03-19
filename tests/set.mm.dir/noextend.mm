include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "con0.mm"
include "crn.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "nofun.mm"
include "cvv.mm"
include "dmexg.mm"
include "funsng.mm"
include "sylancl.mm"
include "elexi.mm"
include "dmsnop.mm"
include "ineq2i.mm"
include "wn.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "funun.mm"
include "syl21anc.mm"
include "csuc.mm"
include "uneq2i.mm"
include "dmun.mm"
include "df-suc.mm"
include "3eqtr4i.mm"
include "nodmon.mm"
include "suceloni.mm"
include "syl5eqel.mm"
include "rnun.mm"
include "rnsnopg.mm"
include "uneq2d.mm"
include "norn.mm"
include "snssi.mm"
include "mp1i.mm"
include "unssd.mm"
include "eqsstrd.mm"
include "elno2.mm"
include "syl3anbrc.mm"

theorem noextend
  let cA: class A
  let cX: class X
  assume noextend.1: |- X e. { 1o , 2o }


  assert |- ( A e. No -> ( A u. { <. dom A , X >. } ) e. No )

  proof
    cA
    csur
    wcel
    #
    cA
    cA
    cdm
    #
    cX
    cop
    csn
    #
    cun
    #
    wfun
    #
    @3
    cdm
    #
    con0
    wcel
    @3
    crn
    #
    c1o
    c2o
    cpr
    #
    wss
    @3
    csur
    wcel
    @0
    cA
    wfun
    @2
    wfun
    #
    @1
    @2
    cdm
    #
    cin
    #
    c0
    wceq
    @4
    cA
    nofun
    @0
    @1
    cvv
    wcel
    #
    cX
    @7
    wcel
    #
    @8
    cA
    csur
    dmexg
    #
    noextend.1
    @1
    cX
    cvv
    @7
    funsng
    sylancl
    @0
    @10
    @1
    @1
    csn
    #
    cin
    #
    c0
    @9
    @14
    @1
    @1
    cX
    cX
    @7
    noextend.1
    elexi
    dmsnop
    #
    ineq2i
    @0
    @1
    @1
    wcel
    wn
    #
    @15
    c0
    wceq
    @0
    @1
    word
    @17
    cA
    nodmord
    @1
    ordirr
    syl
    @1
    @1
    disjsn
    sylibr
    syl5eq
    cA
    @2
    funun
    syl21anc
    @0
    @5
    @1
    csuc
    #
    con0
    @1
    @9
    cun
    @1
    @14
    cun
    @5
    @18
    @9
    @14
    @1
    @16
    uneq2i
    cA
    @2
    dmun
    @1
    df-suc
    3eqtr4i
    @0
    @1
    con0
    wcel
    @18
    con0
    wcel
    cA
    nodmon
    @1
    suceloni
    syl
    syl5eqel
    @0
    @6
    cA
    crn
    #
    cX
    csn
    #
    cun
    #
    @7
    @0
    @6
    @19
    @2
    crn
    #
    cun
    @21
    cA
    @2
    rnun
    @0
    @22
    @20
    @19
    @0
    @11
    @22
    @20
    wceq
    @13
    @1
    cX
    cvv
    rnsnopg
    syl
    uneq2d
    syl5eq
    @0
    @19
    @20
    @7
    cA
    norn
    @12
    @20
    @7
    wss
    @0
    noextend.1
    cX
    @7
    snssi
    mp1i
    unssd
    eqsstrd
    @3
    elno2
    syl3anbrc
end
