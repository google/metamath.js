include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cphtpc.mm"
include "cfv.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "phtpcrel.mm"
include "a1i.mm"
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
include "adantl.mm"
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
include "wb.mm"
include "id.mm"
include "phtpyid.mm"
include "ancli.mm"
include "pm4.71ri.mm"
include "df-3an.mm"
include "3ancomb.mm"
include "3bitr2i.mm"
include "bitr4i.mm"
include "iserd.mm"
include "trud.mm"

theorem phtpcerOLD
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
    cii
    cJ
    ccn
    co
    #
    cJ
    cphtpc
    cfv
    #
    wer
    wtru
    vx
    vy
    vz
    @0
    @1
    @1
    wrel
    wtru
    cJ
    phtpcrel
    a1i
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
    @2
    @1
    wbr
    #
    wtru
    @4
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
    @5
    @4
    @7
    @6
    @2
    @3
    @8
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
    @7
    @6
    @12
    @13
    simp1bi
    #
    @4
    vf
    cv
    #
    @11
    wcel
    #
    @10
    vf
    @4
    @12
    @17
    vf
    wex
    #
    @4
    @7
    @6
    @12
    @13
    simp3bi
    #
    vf
    @11
    n0
    #
    sylib
    @4
    @17
    wa
    #
    vu
    vv
    cc0
    c1
    cicc
    co
    #
    @22
    vu
    cv
    #
    c1
    vv
    cv
    #
    cmin
    co
    @16
    co
    cmpt2
    #
    @9
    wcel
    @10
    @21
    vu
    vv
    @2
    @3
    @16
    cJ
    @25
    @4
    @7
    @17
    @15
    adantr
    @4
    @6
    @17
    @14
    adantr
    @25
    eqid
    @4
    @17
    simpr
    phtpycom
    @9
    @25
    ne0i
    syl
    exlimddv
    @3
    @2
    cJ
    isphtpc
    syl3anbrc
    adantl
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
    @2
    @26
    @1
    wbr
    #
    wtru
    @28
    @7
    @26
    @0
    wcel
    #
    @2
    @26
    @8
    co
    #
    c0
    wne
    #
    @29
    @4
    @7
    @27
    @15
    adantr
    #
    @28
    @6
    @30
    @3
    @26
    @8
    co
    #
    c0
    wne
    #
    @28
    @27
    @6
    @30
    @35
    w3a
    @4
    @27
    simpr
    @3
    @26
    cJ
    isphtpc
    sylib
    #
    simp2d
    #
    @28
    @17
    vg
    cv
    #
    @34
    wcel
    #
    wa
    #
    vg
    wex
    vf
    wex
    #
    @32
    @28
    @18
    @39
    vg
    wex
    #
    @41
    @28
    @12
    @18
    @4
    @12
    @27
    @19
    adantr
    @20
    sylib
    @28
    @35
    @42
    @28
    @6
    @30
    @35
    @36
    simp3d
    vg
    @34
    n0
    sylib
    @17
    @39
    vf
    vg
    eeanv
    sylanbrc
    @28
    @40
    @32
    vf
    vg
    @28
    @40
    @32
    @28
    @40
    wa
    #
    vu
    vv
    @22
    @22
    @24
    c1
    c2
    cdiv
    co
    cle
    wbr
    @23
    c2
    @24
    cmul
    co
    #
    @16
    co
    @23
    @44
    c1
    cmin
    co
    @38
    co
    cif
    cmpt2
    #
    @31
    wcel
    @32
    @43
    vu
    vv
    @2
    @3
    @26
    cJ
    @16
    @38
    @45
    @45
    eqid
    @28
    @7
    @40
    @33
    adantr
    @28
    @6
    @40
    @28
    @6
    @30
    @35
    @36
    simp1d
    adantr
    @28
    @30
    @40
    @37
    adantr
    @28
    @17
    @39
    simprl
    @28
    @17
    @39
    simprr
    phtpycc
    @31
    @45
    ne0i
    syl
    ex
    exlimdvv
    mpd
    @2
    @26
    cJ
    isphtpc
    syl3anbrc
    adantl
    @7
    @2
    @2
    @1
    wbr
    #
    wb
    wtru
    @7
    @7
    @7
    @2
    @2
    @8
    co
    #
    c0
    wne
    #
    w3a
    #
    @46
    @7
    @7
    @48
    wa
    #
    @7
    wa
    @7
    @48
    @7
    w3a
    @49
    @7
    @50
    @7
    @48
    @7
    vy
    vz
    @22
    @22
    @3
    @2
    cfv
    cmpt2
    #
    @47
    wcel
    @48
    @7
    vy
    vz
    @2
    @51
    cJ
    @51
    eqid
    @7
    id
    phtpyid
    @47
    @51
    ne0i
    syl
    ancli
    pm4.71ri
    @7
    @48
    @7
    df-3an
    @7
    @48
    @7
    3ancomb
    3bitr2i
    @2
    @2
    cJ
    isphtpc
    bitr4i
    a1i
    iserd
    trud
end
