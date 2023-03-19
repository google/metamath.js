include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wne.mm"
include "wb.mm"
include "cab.mm"
include "wi.mm"
include "breq2.mm"
include "cbvexvw.mm"
include "wceq.mm"
include "anbi1d.mm"
include "bianir.mm"
include "vex.mm"
include "weq.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "ex.mm"
include "syl.mm"
include "pm2.43a.mm"
include "adantld.mm"
include "wn.mm"
include "nne.mm"
include "notbi.mm"
include "eqcoms.mm"
include "pm2.24.mm"
include "syl6bi.mm"
include "com13.mm"
include "syl5bi.mm"
include "imp.mm"
include "sylbi.mm"
include "pm2.43i.mm"
include "pm2.61i.mm"
include "adantr.mm"
include "com12.mm"
include "pm2.61ine.mm"
include "expcom.mm"
include "exlimiv.mm"
include "a1i.mm"
include "ss2abdv.mm"
include "suppvalbr.mm"
include "cnvimadfsn.mm"
include "3sstr4d.mm"
include "suppimacnvss.mm"
include "eqssd.mm"

theorem suppimacnv
  let cR: class R
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vt: setvar t


  assert |- ( ( R e. V /\ Z e. W ) -> ( R supp Z ) = ( `' R " ( _V \ { Z } ) ) )

  proof
    cR
    cV
    wcel
    cZ
    cW
    wcel
    wa
    #
    cR
    cZ
    csupp
    co
    #
    cR
    ccnv
    cvv
    cZ
    csn
    cdif
    cima
    #
    @0
    vx
    cv
    #
    vt
    cv
    #
    cR
    wbr
    #
    vt
    wex
    #
    @5
    @4
    cZ
    wne
    #
    wb
    #
    vt
    wex
    #
    wa
    #
    vx
    cab
    @3
    vy
    cv
    #
    cR
    wbr
    #
    @11
    cZ
    wne
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    @1
    @2
    @0
    @10
    @15
    vx
    @10
    @15
    wi
    @0
    @6
    @9
    @15
    @6
    @3
    vs
    cv
    #
    cR
    wbr
    #
    vs
    wex
    @9
    @15
    wi
    #
    @5
    @18
    vt
    vs
    @4
    @17
    @3
    cR
    breq2
    cbvexvw
    @18
    @19
    vs
    @9
    @18
    @15
    @8
    @18
    @15
    wi
    vt
    @18
    @8
    @15
    @18
    @8
    wa
    #
    @15
    wi
    @17
    cZ
    @17
    cZ
    wceq
    #
    @20
    @3
    cZ
    cR
    wbr
    #
    @8
    wa
    #
    @15
    @21
    @18
    @22
    @8
    @17
    cZ
    @3
    cR
    breq2
    anbi1d
    @7
    @23
    @15
    wi
    #
    @7
    @8
    @15
    @22
    @8
    @7
    @15
    @7
    @8
    @7
    @15
    wi
    #
    @7
    @8
    wa
    @5
    @25
    @7
    @5
    bianir
    @5
    @7
    @15
    @14
    @5
    @7
    wa
    vy
    @4
    vt
    vex
    vy
    vt
    weq
    @12
    @5
    @13
    @7
    @11
    @4
    @3
    cR
    breq2
    @11
    @4
    cZ
    neeq1
    anbi12d
    spcev
    ex
    syl
    ex
    pm2.43a
    adantld
    @7
    wn
    #
    @24
    @26
    @4
    cZ
    wceq
    #
    @26
    @24
    wi
    @4
    cZ
    nne
    @23
    @26
    @27
    @15
    @22
    @8
    @26
    @27
    @15
    wi
    #
    wi
    @26
    @8
    @22
    @28
    @8
    @5
    wn
    #
    @26
    wb
    #
    @26
    @22
    @28
    wi
    #
    @5
    @7
    notbi
    @26
    @30
    @31
    @26
    @30
    wa
    @29
    @31
    @26
    @29
    bianir
    @27
    @22
    @29
    @15
    @27
    @22
    @5
    @29
    @15
    wi
    @22
    @5
    wb
    cZ
    @4
    cZ
    @4
    @3
    cR
    breq2
    eqcoms
    @5
    @15
    pm2.24
    syl6bi
    com13
    syl
    ex
    syl5bi
    com13
    imp
    com13
    sylbi
    pm2.43i
    pm2.61i
    syl6bi
    @20
    @17
    cZ
    wne
    #
    @15
    @18
    @32
    @15
    wi
    @8
    @18
    @32
    @15
    @14
    @18
    @32
    wa
    vy
    @17
    vs
    vex
    vy
    vs
    weq
    @12
    @18
    @13
    @32
    @11
    @17
    @3
    cR
    breq2
    @11
    @17
    cZ
    neeq1
    anbi12d
    spcev
    ex
    adantr
    com12
    pm2.61ine
    expcom
    exlimiv
    com12
    exlimiv
    sylbi
    imp
    a1i
    ss2abdv
    vx
    vt
    cR
    cV
    cW
    cZ
    suppvalbr
    @2
    @16
    wceq
    @0
    vx
    vy
    cR
    cZ
    cnvimadfsn
    a1i
    3sstr4d
    cR
    cV
    cW
    cZ
    suppimacnvss
    eqssd
end
