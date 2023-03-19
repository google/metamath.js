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
include "3adant3.mm"
include "3adant2.mm"
include "jca.mm"
include "3coml.mm"
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
include "mul12.mm"
include "3adant1r.mm"
include "3expb.mm"
include "ancoms.mm"
include "eqeq1d.mm"
include "mulcl.mm"
include "mulcan.mm"
include "syl3an1.mm"
include "bitr3d.mm"
include "syl3an.mm"
include "3impa.mm"
include "3expia.mm"
include "3impb.mm"
include "imp.mm"
include "biimpd.mm"
include "dvds1lem.mm"
include "dvdscmul.mm"
include "impbid.mm"

theorem dvdscmulr
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ ( K e. ZZ /\ K =/= 0 ) ) -> ( ( K x. M ) || ( K x. N ) <-> M || N ) )

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
    cK
    cM
    cmul
    co
    #
    cK
    cN
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
    #
    @3
    @2
    @0
    @1
    @13
    @2
    @0
    @1
    w3a
    @11
    @12
    @2
    @0
    @11
    @1
    cK
    cM
    zmulcl
    3adant3
    @2
    @1
    @12
    @0
    cK
    cN
    zmulcl
    3adant2
    jca
    3coml
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
    @14
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
    @14
    @16
    @18
    wb
    #
    @0
    @1
    @4
    @14
    @19
    wi
    @0
    @1
    @4
    wa
    #
    @14
    @19
    @14
    @0
    @20
    @19
    @14
    @0
    @20
    @19
    @14
    @0
    wa
    #
    @1
    @4
    @19
    @21
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
    @19
    @14
    @22
    @0
    @23
    @10
    zcn
    cM
    zcn
    anim12i
    cN
    zcn
    @2
    @26
    @3
    cK
    zcn
    anim1i
    @24
    @25
    @27
    w3a
    #
    cK
    @17
    cmul
    co
    #
    @7
    wceq
    #
    @16
    @18
    @28
    @29
    @15
    @7
    @24
    @27
    @29
    @15
    wceq
    #
    @25
    @27
    @24
    @31
    @27
    @22
    @23
    @31
    @26
    @22
    @23
    @31
    @3
    cK
    @10
    cM
    mul12
    3adant1r
    3expb
    ancoms
    3adant2
    eqeq1d
    @24
    @17
    cc
    wcel
    @25
    @27
    @30
    @18
    wb
    @10
    cM
    mulcl
    @17
    cN
    cK
    mulcan
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
    dvdscmul
    3adant3r
    impbid
end
