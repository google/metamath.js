include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cdvds.mm"
include "cn0.mm"
include "crab.mm"
include "csn.mm"
include "ovex.mm"
include "snid.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "elsni.mm"
include "impbii.mm"
include "crio.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "modlt.mm"
include "syl2an.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cc0.mm"
include "wne.mm"
include "nnre.mm"
include "nnne0.mm"
include "redivcl.mm"
include "syl3an.mm"
include "3anidm23.mm"
include "flcld.mm"
include "nnz.mm"
include "adantl.mm"
include "zmodcl.mm"
include "nn0zd.mm"
include "zsubcl.mm"
include "syldan.mm"
include "cc.mm"
include "nncn.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "modval.mm"
include "nn0cnd.mm"
include "zmulcl.mm"
include "syl2an2.mm"
include "zcn.mm"
include "adantr.mm"
include "subexsub.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "dvds0lem.mm"
include "syl31anc.mm"
include "wreu.mm"
include "wb.mm"
include "divalg2.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbi2and.mm"
include "eqcomd.mm"
include "sneqd.mm"
include "snriota.mm"
include "syl.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem divalgmod
  let cD: class D
  let cR: class R
  let cN: class N
  let vz: setvar z


  assert |- ( ( N e. ZZ /\ D e. NN ) -> ( R = ( N mod D ) <-> ( R e. NN0 /\ ( R < D /\ D || ( N - R ) ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    wa
    #
    cR
    cN
    cD
    cmo
    co
    #
    wceq
    #
    cR
    vz
    cv
    #
    cD
    clt
    wbr
    #
    cD
    cN
    @5
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    vz
    cn0
    crab
    #
    wcel
    #
    cR
    cn0
    wcel
    cR
    cD
    clt
    wbr
    #
    cD
    cN
    cR
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    @4
    cR
    @3
    csn
    #
    wcel
    #
    @2
    @11
    @4
    @17
    @4
    @17
    @3
    @16
    wcel
    @3
    cN
    cD
    cmo
    ovex
    snid
    cR
    @3
    @16
    eleq1
    mpbiri
    cR
    @3
    elsni
    impbii
    @2
    @16
    @10
    cR
    @2
    @16
    @9
    vz
    cn0
    crio
    #
    csn
    #
    @10
    @2
    @3
    @18
    @2
    @18
    @3
    @2
    @3
    cD
    clt
    wbr
    #
    cD
    cN
    @3
    cmin
    co
    #
    cdvds
    wbr
    #
    @18
    @3
    wceq
    #
    @0
    cN
    cr
    wcel
    #
    cD
    crp
    wcel
    #
    @20
    @1
    cN
    zre
    #
    cD
    nnrp
    #
    cN
    cD
    modlt
    syl2an
    @2
    cN
    cD
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    @21
    cz
    wcel
    #
    @29
    cD
    cmul
    co
    #
    @21
    wceq
    @22
    @2
    @28
    @0
    @1
    @28
    cr
    wcel
    #
    @0
    @24
    @1
    cD
    cr
    wcel
    @1
    cD
    cc0
    wne
    @34
    @26
    cD
    nnre
    cD
    nnne0
    cN
    cD
    redivcl
    syl3an
    3anidm23
    flcld
    #
    @1
    @31
    @0
    cD
    nnz
    #
    adantl
    @0
    @1
    @3
    cz
    wcel
    @32
    @2
    @3
    cN
    cD
    zmodcl
    #
    nn0zd
    cN
    @3
    zsubcl
    syldan
    @2
    cD
    @29
    cmul
    co
    #
    @33
    @21
    @2
    cD
    @29
    @1
    cD
    cc
    wcel
    @0
    cD
    nncn
    adantl
    @2
    @29
    @35
    zcnd
    mulcomd
    @2
    @3
    cN
    @38
    cmin
    co
    wceq
    #
    @38
    @21
    wceq
    @0
    @24
    @25
    @39
    @1
    @26
    @27
    cN
    cD
    modval
    syl2an
    @2
    @3
    @38
    cN
    @2
    @3
    @37
    nn0cnd
    @2
    @38
    @1
    @31
    @0
    @30
    @38
    cz
    wcel
    @36
    @35
    cD
    @29
    zmulcl
    syl2an2
    zcnd
    @0
    cN
    cc
    wcel
    @1
    cN
    zcn
    adantr
    subexsub
    mpbid
    eqtr3d
    @29
    cD
    @21
    dvds0lem
    syl31anc
    @2
    @3
    cn0
    wcel
    @9
    vz
    cn0
    wreu
    #
    @20
    @22
    wa
    #
    @23
    wb
    @37
    cD
    cN
    vz
    divalg2
    #
    @9
    @41
    vz
    cn0
    @3
    @5
    @3
    wceq
    #
    @6
    @20
    @8
    @22
    @5
    @3
    cD
    clt
    breq1
    @43
    @7
    @21
    cD
    cdvds
    @5
    @3
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    riota2
    syl2anc
    mpbi2and
    eqcomd
    sneqd
    @2
    @40
    @10
    @19
    wceq
    @42
    @9
    vz
    cn0
    snriota
    syl
    eqtr4d
    eleq2d
    syl5bb
    @9
    @15
    vz
    cR
    cn0
    @5
    cR
    wceq
    #
    @6
    @12
    @8
    @14
    @5
    cR
    cD
    clt
    breq1
    @44
    @7
    @13
    cD
    cdvds
    @5
    cR
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    elrab
    syl6bb
end
