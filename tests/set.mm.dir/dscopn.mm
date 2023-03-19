include "wcel.mm"
include "cmopn.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "wral.mm"
include "cxmt.mm"
include "wb.mm"
include "cme.mm"
include "dscmet.mm"
include "metxmet.mm"
include "syl.mm"
include "eqid.mm"
include "elmopn.mm"
include "simpll.mm"
include "ssel2.mm"
include "adantll.mm"
include "jca.mm"
include "csn.mm"
include "c1.mm"
include "co.mm"
include "wceq.mm"
include "velsn.mm"
include "clt.mm"
include "wbr.mm"
include "eleq1a.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "cc0.mm"
include "cif.mm"
include "eqeq12.mm"
include "ifbid.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "keepel.mm"
include "elexi.mm"
include "ovmpt2a.mm"
include "breq1d.mm"
include "wn.mm"
include "ltnri.mm"
include "iffalse.mm"
include "mtbiri.mm"
include "con4i.mm"
include "iftrue.mm"
include "0lt1.mm"
include "syl6eqbr.mm"
include "impbii.mm"
include "equcom.mm"
include "bitri.mm"
include "syl6rbb.mm"
include "simpr.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "adantl.mm"
include "cxr.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "elbl.mm"
include "mp3an3.mm"
include "sylan.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "blelrn.mm"
include "eqeltrd.mm"
include "snssi.mm"
include "vsnid.mm"
include "jctil.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "sylancom.mm"
include "ralrimiva.mm"
include "pm4.71d.mm"
include "selpw.mm"
include "syl6bbr.mm"

theorem dscopn
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume dscmet.1: |- D = ( x e. X , y e. X |-> if ( x = y , 0 , 1 ) )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u w
  disjoint D u
  disjoint v w
  disjoint D v
  disjoint D w
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint u x
  disjoint u y
  disjoint X u
  disjoint v x
  disjoint v y
  disjoint X v
  disjoint w x
  disjoint w y
  disjoint X w
  assert |- ( X e. V -> ( MetOpen ` D ) = ~P X )

  proof
    cX
    cV
    wcel
    #
    vu
    cD
    cmopn
    cfv
    #
    cX
    cpw
    #
    @0
    vu
    cv
    #
    @1
    wcel
    #
    @3
    cX
    wss
    #
    @3
    @2
    wcel
    @0
    @4
    @5
    vv
    cv
    #
    vw
    cv
    #
    wcel
    #
    @7
    @3
    wss
    #
    wa
    #
    vw
    cD
    cbl
    cfv
    #
    crn
    #
    wrex
    #
    vv
    @3
    wral
    #
    wa
    #
    @5
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @4
    @15
    wb
    @0
    cD
    cX
    cme
    cfv
    wcel
    @16
    vx
    vy
    cD
    cV
    cX
    dscmet.1
    dscmet
    cD
    cX
    metxmet
    syl
    #
    vv
    vw
    @3
    cD
    @1
    cX
    @1
    eqid
    elmopn
    syl
    @0
    @5
    @14
    @0
    @5
    @14
    @0
    @5
    wa
    #
    @13
    vv
    @3
    @18
    @6
    @3
    wcel
    #
    @0
    @6
    cX
    wcel
    #
    wa
    #
    @13
    @18
    @19
    wa
    @0
    @20
    @0
    @5
    @19
    simpll
    @5
    @19
    @20
    @0
    @3
    cX
    @6
    ssel2
    adantll
    jca
    @21
    @6
    csn
    #
    @12
    wcel
    @6
    @22
    wcel
    #
    @22
    @3
    wss
    #
    wa
    #
    @13
    @19
    @21
    @22
    @6
    c1
    @11
    co
    #
    @12
    @21
    vw
    @22
    @26
    @7
    @22
    wcel
    @7
    @6
    wceq
    #
    @21
    @7
    @26
    wcel
    #
    vw
    @6
    velsn
    @21
    @27
    @7
    cX
    wcel
    #
    @6
    @7
    cD
    co
    #
    c1
    clt
    wbr
    #
    wa
    #
    @28
    @20
    @27
    @32
    wb
    #
    @0
    @20
    @29
    @27
    @32
    @6
    cX
    @7
    eleq1a
    @32
    @29
    wi
    @20
    @29
    @31
    simpl
    a1i
    @20
    @29
    @33
    @20
    @29
    wa
    #
    @27
    @31
    @32
    @34
    @31
    @6
    @7
    wceq
    #
    cc0
    c1
    cif
    #
    c1
    clt
    wbr
    #
    @27
    @34
    @30
    @36
    c1
    clt
    vx
    vy
    @6
    @7
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    cc0
    c1
    cif
    @36
    cD
    @38
    @6
    wceq
    @39
    @7
    wceq
    wa
    @40
    @35
    cc0
    c1
    @38
    @6
    @39
    @7
    eqeq12
    ifbid
    dscmet.1
    @36
    cr
    @35
    cc0
    c1
    cr
    0re
    1re
    keepel
    elexi
    ovmpt2a
    breq1d
    @37
    @35
    @27
    @37
    @35
    @35
    @37
    @35
    wn
    #
    @37
    c1
    c1
    clt
    wbr
    c1
    1re
    ltnri
    @41
    @36
    c1
    c1
    clt
    @35
    cc0
    c1
    iffalse
    breq1d
    mtbiri
    con4i
    @35
    @36
    cc0
    c1
    clt
    @35
    cc0
    c1
    iftrue
    0lt1
    syl6eqbr
    impbii
    vv
    vw
    equcom
    bitri
    syl6rbb
    @34
    @29
    @31
    @20
    @29
    simpr
    biantrurd
    bitrd
    ex
    pm5.21ndd
    adantl
    @0
    @16
    @20
    @28
    @32
    wb
    #
    @17
    @16
    @20
    c1
    cxr
    wcel
    #
    @42
    c1
    crp
    wcel
    @43
    1rp
    c1
    rpxr
    ax-mp
    #
    @7
    cD
    @6
    c1
    cX
    elbl
    mp3an3
    sylan
    bitr4d
    syl5bb
    eqrdv
    @0
    @16
    @20
    @26
    @12
    wcel
    #
    @17
    @16
    @20
    @43
    @45
    @44
    cD
    @6
    c1
    cX
    blelrn
    mp3an3
    sylan
    eqeltrd
    @19
    @24
    @23
    @6
    @3
    snssi
    vv
    vsnid
    jctil
    @10
    @25
    vw
    @22
    @12
    @7
    @22
    wceq
    @8
    @23
    @9
    @24
    @7
    @22
    @6
    eleq2
    @7
    @22
    @3
    sseq1
    anbi12d
    rspcev
    syl2an
    sylancom
    ralrimiva
    ex
    pm4.71d
    bitr4d
    vu
    cX
    selpw
    syl6bbr
    eqrdv
end
