include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cphtpc.mm"
include "cfv.mm"
include "phtpcrel.mm"
include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "isphtpc.mm"
include "simp2bi.mm"
include "simp1bi.mm"
include "wex.mm"
include "simp3bi.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cmin.mm"
include "cmpt2.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr.mm"
include "phtpycom.mm"
include "ne0i.mm"
include "syl.mm"
include "exlimddv.mm"
include "syl3anbrc.mm"
include "w3a.mm"
include "simp2d.mm"
include "simp3d.mm"
include "eeanv.mm"
include "sylanbrc.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "cmul.mm"
include "cif.mm"
include "simp1d.mm"
include "simprl.mm"
include "simprr.mm"
include "phtpycc.mm"
include "ex.mm"
include "exlimdvv.mm"
include "mpd.mm"
include "id.mm"
include "phtpyid.mm"
include "ancli.mm"
include "pm4.71ri.mm"
include "df-3an.mm"
include "3ancomb.mm"
include "3bitr2i.mm"
include "bitr4i.mm"
include "iseri.mm"

theorem phtpcer
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ~=ph ` J ) Er ( II Cn J )

  proof
    vx
    vy
    vz
    cii
    cJ
    ccn
    co
    #
    cJ
    cphtpc
    cfv
    #
    cJ
    phtpcrel
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    #
    @3
    @0
    wcel
    #
    @2
    @0
    wcel
    #
    @3
    @2
    cJ
    cphtpy
    cfv
    #
    co
    #
    c0
    wne
    #
    @3
    @2
    @1
    wbr
    @4
    @6
    @5
    @2
    @3
    @7
    co
    #
    c0
    wne
    #
    @2
    @3
    cJ
    isphtpc
    #
    simp2bi
    #
    @4
    @6
    @5
    @11
    @12
    simp1bi
    #
    @4
    vf
    cv
    #
    @10
    wcel
    #
    @9
    vf
    @4
    @11
    @16
    vf
    wex
    #
    @4
    @6
    @5
    @11
    @12
    simp3bi
    #
    vf
    @10
    n0
    #
    sylib
    @4
    @16
    wa
    #
    vu
    vv
    cc0
    c1
    cicc
    co
    #
    @21
    vu
    cv
    #
    c1
    vv
    cv
    #
    cmin
    co
    @15
    co
    cmpt2
    #
    @8
    wcel
    @9
    @20
    vu
    vv
    @2
    @3
    @15
    cJ
    @24
    @4
    @6
    @16
    @14
    adantr
    @4
    @5
    @16
    @13
    adantr
    @24
    eqid
    @4
    @16
    simpr
    phtpycom
    @8
    @24
    ne0i
    syl
    exlimddv
    @3
    @2
    cJ
    isphtpc
    syl3anbrc
    @4
    @3
    vz
    cv
    #
    @1
    wbr
    #
    wa
    #
    @6
    @25
    @0
    wcel
    #
    @2
    @25
    @7
    co
    #
    c0
    wne
    #
    @2
    @25
    @1
    wbr
    @4
    @6
    @26
    @14
    adantr
    #
    @27
    @5
    @28
    @3
    @25
    @7
    co
    #
    c0
    wne
    #
    @27
    @26
    @5
    @28
    @33
    w3a
    @4
    @26
    simpr
    @3
    @25
    cJ
    isphtpc
    sylib
    #
    simp2d
    #
    @27
    @16
    vg
    cv
    #
    @32
    wcel
    #
    wa
    #
    vg
    wex
    vf
    wex
    #
    @30
    @27
    @17
    @37
    vg
    wex
    #
    @39
    @27
    @11
    @17
    @4
    @11
    @26
    @18
    adantr
    @19
    sylib
    @27
    @33
    @40
    @27
    @5
    @28
    @33
    @34
    simp3d
    vg
    @32
    n0
    sylib
    @16
    @37
    vf
    vg
    eeanv
    sylanbrc
    @27
    @38
    @30
    vf
    vg
    @27
    @38
    @30
    @27
    @38
    wa
    #
    vu
    vv
    @21
    @21
    @23
    c1
    c2
    cdiv
    co
    cle
    wbr
    @22
    c2
    @23
    cmul
    co
    #
    @15
    co
    @22
    @42
    c1
    cmin
    co
    @36
    co
    cif
    cmpt2
    #
    @29
    wcel
    @30
    @41
    vu
    vv
    @2
    @3
    @25
    cJ
    @15
    @36
    @43
    @43
    eqid
    @27
    @6
    @38
    @31
    adantr
    @27
    @5
    @38
    @27
    @5
    @28
    @33
    @34
    simp1d
    adantr
    @27
    @28
    @38
    @35
    adantr
    @27
    @16
    @37
    simprl
    @27
    @16
    @37
    simprr
    phtpycc
    @29
    @43
    ne0i
    syl
    ex
    exlimdvv
    mpd
    @2
    @25
    cJ
    isphtpc
    syl3anbrc
    @6
    @6
    @6
    @2
    @2
    @7
    co
    #
    c0
    wne
    #
    w3a
    #
    @2
    @2
    @1
    wbr
    @6
    @6
    @45
    wa
    #
    @6
    wa
    @6
    @45
    @6
    w3a
    @46
    @6
    @47
    @6
    @45
    @6
    vy
    vz
    @21
    @21
    @3
    @2
    cfv
    cmpt2
    #
    @44
    wcel
    @45
    @6
    vy
    vz
    @2
    @48
    cJ
    @48
    eqid
    @6
    id
    phtpyid
    @44
    @48
    ne0i
    syl
    ancli
    pm4.71ri
    @6
    @45
    @6
    df-3an
    @6
    @45
    @6
    3ancomb
    3bitr2i
    @2
    @2
    cJ
    isphtpc
    bitr4i
    iseri
end
