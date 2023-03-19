include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "rescom.mm"
include "uneq1i.mm"
include "un23.mm"
include "eqtri.mm"
include "wceq.mm"
include "setsval.mm"
include "ad2ant2r.mm"
include "reseq1d.mm"
include "resundir.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "cxp.mm"
include "elex.mm"
include "ad2antrl.mm"
include "opelxpi.mm"
include "sylancr.mm"
include "opex.mm"
include "relsn.mm"
include "sylibr.mm"
include "dmsnopss.mm"
include "cin.mm"
include "c0.mm"
include "disjsn2.mm"
include "ad2antlr.mm"
include "disj2.mm"
include "sylib.mm"
include "syl5ss.mm"
include "relssres.mm"
include "syl2anc.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "uneq1d.mm"
include "ad2ant2rl.mm"
include "ad2antll.mm"
include "wb.mm"
include "ssv.mm"
include "ssconb.mm"
include "mp2an.mm"
include "3eqtr4a.mm"
include "ovex.mm"
include "simprr.mm"
include "simprl.mm"
include "3eqtr4d.mm"

theorem setscom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cV: class V
  let cW: class W
  let cX: class X
  assume setscom.1: |- A e. _V
  assume setscom.2: |- B e. _V


  assert |- ( ( ( S e. V /\ A =/= B ) /\ ( C e. W /\ D e. X ) ) -> ( ( S sSet <. A , C >. ) sSet <. B , D >. ) = ( ( S sSet <. B , D >. ) sSet <. A , C >. ) )

  proof
    cS
    cV
    wcel
    #
    cA
    cB
    wne
    #
    wa
    #
    cC
    cW
    wcel
    #
    cD
    cX
    wcel
    #
    wa
    #
    wa
    #
    cS
    cA
    cC
    cop
    #
    csts
    co
    #
    cvv
    cB
    csn
    #
    cdif
    #
    cres
    #
    cB
    cD
    cop
    #
    csn
    #
    cun
    #
    cS
    @12
    csts
    co
    #
    cvv
    cA
    csn
    #
    cdif
    #
    cres
    #
    @7
    csn
    #
    cun
    #
    @8
    @12
    csts
    co
    #
    @15
    @7
    csts
    co
    #
    @6
    cS
    @17
    cres
    #
    @10
    cres
    #
    @19
    cun
    #
    @13
    cun
    #
    cS
    @10
    cres
    #
    @17
    cres
    #
    @13
    cun
    #
    @19
    cun
    #
    @14
    @20
    @26
    @28
    @19
    cun
    #
    @13
    cun
    @30
    @25
    @31
    @13
    @24
    @28
    @19
    cS
    @17
    @10
    rescom
    uneq1i
    uneq1i
    @28
    @19
    @13
    un23
    eqtri
    @6
    @11
    @25
    @13
    @6
    @11
    @23
    @19
    cun
    #
    @10
    cres
    #
    @25
    @6
    @8
    @32
    @10
    @0
    @3
    @8
    @32
    wceq
    @1
    @4
    cA
    cC
    cS
    cV
    cW
    setsval
    ad2ant2r
    reseq1d
    @6
    @33
    @24
    @19
    @10
    cres
    #
    cun
    @25
    @23
    @19
    @10
    resundir
    @6
    @34
    @19
    @24
    @6
    @19
    wrel
    #
    @19
    cdm
    #
    @10
    wss
    @34
    @19
    wceq
    @6
    @7
    cvv
    cvv
    cxp
    #
    wcel
    #
    @35
    @6
    cA
    cvv
    wcel
    cC
    cvv
    wcel
    #
    @38
    setscom.1
    @3
    @39
    @2
    @4
    cC
    cW
    elex
    ad2antrl
    cA
    cC
    cvv
    cvv
    opelxpi
    sylancr
    @7
    cA
    cC
    opex
    relsn
    sylibr
    @6
    @36
    @16
    @10
    cA
    cC
    dmsnopss
    @6
    @16
    @9
    cin
    c0
    wceq
    #
    @16
    @10
    wss
    #
    @1
    @40
    @0
    @5
    cA
    cB
    disjsn2
    ad2antlr
    @16
    @9
    disj2
    sylib
    #
    syl5ss
    @19
    @10
    relssres
    syl2anc
    uneq2d
    syl5eq
    eqtrd
    uneq1d
    @6
    @18
    @29
    @19
    @6
    @18
    @27
    @13
    cun
    #
    @17
    cres
    #
    @29
    @0
    @4
    @18
    @44
    wceq
    @1
    @3
    @0
    @4
    wa
    @15
    @43
    @17
    cB
    cD
    cS
    cV
    cX
    setsval
    reseq1d
    ad2ant2rl
    @6
    @44
    @28
    @13
    @17
    cres
    #
    cun
    @29
    @27
    @13
    @17
    resundir
    @6
    @45
    @13
    @28
    @6
    @13
    wrel
    #
    @13
    cdm
    #
    @17
    wss
    @45
    @13
    wceq
    @6
    @12
    @37
    wcel
    #
    @46
    @6
    cB
    cvv
    wcel
    cD
    cvv
    wcel
    #
    @48
    setscom.2
    @4
    @49
    @2
    @3
    cD
    cX
    elex
    ad2antll
    cB
    cD
    cvv
    cvv
    opelxpi
    sylancr
    @12
    cB
    cD
    opex
    relsn
    sylibr
    @6
    @47
    @9
    @17
    cB
    cD
    dmsnopss
    @6
    @41
    @9
    @17
    wss
    #
    @42
    @16
    cvv
    wss
    @9
    cvv
    wss
    @41
    @50
    wb
    @16
    ssv
    @9
    ssv
    @16
    @9
    cvv
    ssconb
    mp2an
    sylib
    syl5ss
    @13
    @17
    relssres
    syl2anc
    uneq2d
    syl5eq
    eqtrd
    uneq1d
    3eqtr4a
    @6
    @8
    cvv
    wcel
    @4
    @21
    @14
    wceq
    cS
    @7
    csts
    ovex
    @2
    @3
    @4
    simprr
    cB
    cD
    @8
    cvv
    cX
    setsval
    sylancr
    @6
    @15
    cvv
    wcel
    @3
    @22
    @20
    wceq
    cS
    @12
    csts
    ovex
    @2
    @3
    @4
    simprl
    cA
    cC
    @15
    cvv
    cW
    setsval
    sylancr
    3eqtr4d
end
