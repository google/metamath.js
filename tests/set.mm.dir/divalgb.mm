include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wreu.mm"
include "cmin.mm"
include "cdvds.mm"
include "wa.mm"
include "cn0.mm"
include "wb.mm"
include "wne.mm"
include "zsubcl.mm"
include "divides.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com12.mm"
include "wi.mm"
include "cc.mm"
include "zcn.mm"
include "zmulcl.mm"
include "zcnd.mm"
include "subadd.mm"
include "syl3an.mm"
include "addcom.mm"
include "syl2an.mm"
include "3adant1.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "eqcom.mm"
include "3bitr3g.mm"
include "3expia.mm"
include "expcomd.mm"
include "3impia.mm"
include "imp.mm"
include "rexbidva.mm"
include "3com23.mm"
include "anbi2d.mm"
include "df-3an.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "anass.mm"
include "syl6bb.mm"
include "3expa.mm"
include "reubidva.mm"
include "weu.mm"
include "elnn0z.mm"
include "anbi1i.mm"
include "eubii.mm"
include "df-reu.mm"
include "3bitr4ri.mm"
include "3adant3.mm"

theorem divalgb
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vq: setvar q

  disjoint D q
  disjoint D r
  disjoint q r
  disjoint N q
  disjoint N r
  assert |- ( ( N e. ZZ /\ D e. ZZ /\ D =/= 0 ) -> ( E! r e. ZZ E. q e. ZZ ( 0 <_ r /\ r < ( abs ` D ) /\ N = ( ( q x. D ) + r ) ) <-> E! r e. NN0 ( r < ( abs ` D ) /\ D || ( N - r ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    cc0
    vr
    cv
    #
    cle
    wbr
    #
    @2
    cD
    cabs
    cfv
    clt
    wbr
    #
    cN
    vq
    cv
    #
    cD
    cmul
    co
    #
    @2
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vr
    cz
    wreu
    #
    @4
    cD
    cN
    @2
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    vr
    cn0
    wreu
    #
    wb
    cD
    cc0
    wne
    @0
    @1
    wa
    #
    @11
    @3
    @14
    wa
    #
    vr
    cz
    wreu
    #
    @15
    @16
    @10
    @17
    vr
    cz
    @0
    @1
    @2
    cz
    wcel
    #
    @10
    @17
    wb
    @0
    @1
    @19
    w3a
    #
    @10
    @3
    @4
    wa
    #
    @13
    wa
    #
    @17
    @20
    @22
    @21
    @8
    vq
    cz
    wrex
    #
    wa
    #
    @10
    @20
    @13
    @23
    @21
    @20
    @13
    @6
    @12
    wceq
    #
    vq
    cz
    wrex
    #
    @23
    @1
    @0
    @19
    @13
    @26
    wb
    #
    @1
    @0
    @19
    @27
    @0
    @19
    wa
    #
    @1
    @12
    cz
    wcel
    @27
    cN
    @2
    zsubcl
    vq
    cD
    @12
    divides
    sylan2
    3impb
    3com12
    @0
    @19
    @1
    @26
    @23
    wb
    @0
    @19
    @1
    w3a
    #
    @25
    @8
    vq
    cz
    @29
    @5
    cz
    wcel
    #
    @25
    @8
    wb
    #
    @0
    @19
    @1
    @30
    @31
    wi
    @28
    @30
    @1
    @31
    @0
    @19
    @30
    @1
    wa
    #
    @31
    @0
    @19
    @32
    w3a
    #
    @12
    @6
    wceq
    #
    @7
    cN
    wceq
    #
    @25
    @8
    @33
    @34
    @2
    @6
    caddc
    co
    #
    cN
    wceq
    #
    @35
    @0
    cN
    cc
    wcel
    @19
    @2
    cc
    wcel
    #
    @32
    @6
    cc
    wcel
    #
    @34
    @37
    wb
    cN
    zcn
    @2
    zcn
    #
    @32
    @6
    @5
    cD
    zmulcl
    zcnd
    #
    cN
    @2
    @6
    subadd
    syl3an
    @33
    @36
    @7
    cN
    @19
    @32
    @36
    @7
    wceq
    #
    @0
    @19
    @38
    @39
    @42
    @32
    @40
    @41
    @2
    @6
    addcom
    syl2an
    3adant1
    eqeq1d
    bitrd
    @12
    @6
    eqcom
    @7
    cN
    eqcom
    3bitr3g
    3expia
    expcomd
    3impia
    imp
    rexbidva
    3com23
    bitrd
    anbi2d
    @10
    @21
    @8
    wa
    #
    vq
    cz
    wrex
    @24
    @9
    @43
    vq
    cz
    @3
    @4
    @8
    df-3an
    rexbii
    @21
    @8
    vq
    cz
    r19.42v
    bitri
    syl6rbbr
    @3
    @4
    @13
    anass
    syl6bb
    3expa
    reubidva
    @2
    cn0
    wcel
    #
    @14
    wa
    #
    vr
    weu
    @19
    @17
    wa
    #
    vr
    weu
    @15
    @18
    @45
    @46
    vr
    @45
    @19
    @3
    wa
    #
    @14
    wa
    @46
    @44
    @47
    @14
    @2
    elnn0z
    anbi1i
    @19
    @3
    @14
    anass
    bitri
    eubii
    @14
    vr
    cn0
    df-reu
    @17
    vr
    cz
    df-reu
    3bitr4ri
    syl6bb
    3adant3
end
