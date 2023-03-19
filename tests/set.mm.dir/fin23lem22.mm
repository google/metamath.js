include "com.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "cen.mm"
include "wbr.mm"
include "crio.mm"
include "ccrd.mm"
include "cfv.mm"
include "wreu.mm"
include "fin23lem23.mm"
include "riotacl.mm"
include "syl.mm"
include "simpll.mm"
include "simpr.mm"
include "sseldd.mm"
include "nnfi.mm"
include "infi.mm"
include "ficardom.mm"
include "4syl.mm"
include "wceq.mm"
include "wb.mm"
include "cardnn.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ad2antrl.mm"
include "cdm.mm"
include "con0.mm"
include "simprr.mm"
include "nnon.mm"
include "onenon.mm"
include "3syl.mm"
include "inss1.mm"
include "ssnum.mm"
include "sylancl.mm"
include "carden2.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "ineq1.mm"
include "breq1d.mm"
include "riota2.mm"
include "3bitrd.mm"
include "f1o2d.mm"

theorem fin23lem22
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  assume fin23lem22.b: |- C = ( i e. _om |-> ( iota_ j e. S ( j i^i S ) ~~ i ) )

  disjoint i j
  disjoint S i
  disjoint S j
  disjoint a i
  disjoint b i
  disjoint a j
  disjoint b j
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint C a
  disjoint C b
  assert |- ( ( S C_ _om /\ -. S e. Fin ) -> C : _om -1-1-onto-> S )

  proof
    cS
    com
    wss
    #
    cS
    cfn
    wcel
    wn
    #
    wa
    #
    vi
    va
    com
    cS
    vj
    cv
    #
    cS
    cin
    #
    vi
    cv
    #
    cen
    wbr
    #
    vj
    cS
    crio
    #
    va
    cv
    #
    cS
    cin
    #
    ccrd
    cfv
    #
    cC
    fin23lem22.b
    @2
    @5
    com
    wcel
    #
    wa
    @6
    vj
    cS
    wreu
    #
    @7
    cS
    wcel
    cS
    vi
    vj
    fin23lem23
    #
    @6
    vj
    cS
    riotacl
    syl
    @2
    @8
    cS
    wcel
    #
    wa
    #
    @8
    com
    wcel
    #
    @8
    cfn
    wcel
    @9
    cfn
    wcel
    @10
    com
    wcel
    @15
    cS
    com
    @8
    @0
    @1
    @14
    simpll
    @2
    @14
    simpr
    sseldd
    @8
    nnfi
    @8
    cS
    infi
    @9
    ficardom
    4syl
    @2
    @11
    @14
    wa
    #
    wa
    #
    @5
    @10
    wceq
    #
    @10
    @5
    ccrd
    cfv
    #
    wceq
    #
    @9
    @5
    cen
    wbr
    #
    @8
    @7
    wceq
    #
    @11
    @19
    @21
    wb
    @2
    @14
    @11
    @19
    @20
    @10
    wceq
    @21
    @11
    @5
    @20
    @10
    @11
    @20
    @5
    @5
    cardnn
    eqcomd
    eqeq1d
    @20
    @10
    eqcom
    syl6bb
    ad2antrl
    @18
    @9
    ccrd
    cdm
    #
    wcel
    #
    @5
    @24
    wcel
    #
    @21
    @22
    wb
    @18
    @8
    @24
    wcel
    #
    @9
    @8
    wss
    @25
    @18
    @16
    @8
    con0
    wcel
    @27
    @18
    cS
    com
    @8
    @0
    @1
    @17
    simpll
    @2
    @11
    @14
    simprr
    #
    sseldd
    @8
    nnon
    @8
    onenon
    3syl
    @8
    cS
    inss1
    @8
    @9
    ssnum
    sylancl
    @18
    @5
    con0
    wcel
    #
    @26
    @11
    @29
    @2
    @14
    @5
    nnon
    ad2antrl
    @5
    onenon
    syl
    @9
    @5
    carden2
    syl2anc
    @18
    @22
    @7
    @8
    wceq
    #
    @23
    @18
    @14
    @12
    @22
    @30
    wb
    @28
    @2
    @11
    @12
    @14
    @13
    adantrr
    @6
    @22
    vj
    cS
    @8
    @3
    @8
    wceq
    @4
    @9
    @5
    cen
    @3
    @8
    cS
    ineq1
    breq1d
    riota2
    syl2anc
    @7
    @8
    eqcom
    syl6bb
    3bitrd
    f1o2d
end
