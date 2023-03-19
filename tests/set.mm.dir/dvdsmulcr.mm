include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "zmulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "jca.mm"
include "3adant3r.mm"
include "3simpa.mm"
include "simpr.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "cc.mm"
include "zcn.mm"
include "anim12i.mm"
include "anim1i.mm"
include "mulass.mm"
include "3expa.mm"
include "adantrr.mm"
include "eqeq1d.mm"
include "mulcl.mm"
include "mulcan2.mm"
include "syl3an1.mm"
include "bitr3d.mm"
include "syl3an.mm"
include "3expb.mm"
include "3impa.mm"
include "3coml.mm"
include "3expia.mm"
include "3impb.mm"
include "imp.mm"
include "biimpd.mm"
include "dvds1lem.mm"
include "dvdsmulc.mm"
include "impbid.mm"

theorem dvdsmulcr
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ ( K e. ZZ /\ K =/= 0 ) ) -> ( ( M x. K ) || ( N x. K ) <-> M || N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cM
    cK
    cmul
    co
    #
    cN
    cK
    cmul
    co
    #
    cdvds
    wbr
    #
    cM
    cN
    cdvds
    wbr
    #
    @5
    vx
    @6
    @7
    cM
    cN
    vx
    cv
    #
    @0
    @1
    @2
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    wa
    @3
    @0
    @1
    @2
    w3a
    @11
    @12
    @0
    @2
    @11
    @1
    cM
    cK
    zmulcl
    3adant2
    @1
    @2
    @12
    @0
    cN
    cK
    zmulcl
    3adant1
    jca
    3adant3r
    @0
    @1
    @4
    3simpa
    @5
    @10
    cz
    wcel
    #
    simpr
    @5
    @13
    wa
    @10
    @6
    cmul
    co
    #
    @7
    wceq
    #
    @10
    cM
    cmul
    co
    #
    cN
    wceq
    #
    @5
    @13
    @15
    @17
    wb
    #
    @0
    @1
    @4
    @13
    @18
    wi
    @0
    @1
    @4
    wa
    #
    @13
    @18
    @13
    @0
    @19
    @18
    @13
    @0
    @19
    @18
    @13
    @0
    wa
    #
    @1
    @4
    @18
    @20
    @10
    cc
    wcel
    #
    cM
    cc
    wcel
    #
    wa
    #
    @1
    cN
    cc
    wcel
    #
    @4
    cK
    cc
    wcel
    #
    @3
    wa
    #
    @18
    @13
    @21
    @0
    @22
    @10
    zcn
    cM
    zcn
    anim12i
    cN
    zcn
    @2
    @25
    @3
    cK
    zcn
    anim1i
    @23
    @24
    @26
    w3a
    #
    @16
    cK
    cmul
    co
    #
    @7
    wceq
    #
    @15
    @17
    @27
    @28
    @14
    @7
    @23
    @26
    @28
    @14
    wceq
    #
    @24
    @23
    @25
    @30
    @3
    @21
    @22
    @25
    @30
    @10
    cM
    cK
    mulass
    3expa
    adantrr
    3adant2
    eqeq1d
    @23
    @16
    cc
    wcel
    @24
    @26
    @29
    @17
    wb
    @10
    cM
    mulcl
    @16
    cN
    cK
    mulcan2
    syl3an1
    bitr3d
    syl3an
    3expb
    3impa
    3coml
    3expia
    3impb
    imp
    biimpd
    dvds1lem
    @0
    @1
    @2
    @9
    @8
    wi
    @3
    cK
    cM
    cN
    dvdsmulc
    3adant3r
    impbid
end
