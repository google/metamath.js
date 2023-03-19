include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cmo.mm"
include "co.mm"
include "csn.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cdvds.mm"
include "cn0.mm"
include "crab.mm"
include "wceq.mm"
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
include "wb.mm"
include "zcn.mm"
include "adantr.mm"
include "zmulcl.mm"
include "anabss7.mm"
include "nn0cnd.mm"
include "subsub23.mm"
include "syl3anc.mm"
include "eqcom.mm"
include "3bitr3g.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "dvds0lem.mm"
include "syl31anc.mm"
include "wreu.mm"
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
include "velsn.mm"
include "elrab.mm"

theorem divalgmodOLD
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vz: setvar z

  disjoint D r
  disjoint N r
  disjoint D z
  disjoint r z
  disjoint N z
  assert |- ( ( N e. ZZ /\ D e. NN ) -> ( r = ( N mod D ) <-> ( r e. NN0 /\ ( r < D /\ D || ( N - r ) ) ) ) )

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
    vr
    cv
    #
    cN
    cD
    cmo
    co
    #
    csn
    #
    wcel
    @3
    vz
    cv
    #
    cD
    clt
    wbr
    #
    cD
    cN
    @6
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
    @3
    @4
    wceq
    @3
    cn0
    wcel
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
    wa
    #
    wa
    @2
    @5
    @11
    @3
    @2
    @5
    @10
    vz
    cn0
    crio
    #
    csn
    #
    @11
    @2
    @4
    @16
    @2
    @16
    @4
    @2
    @4
    cD
    clt
    wbr
    #
    cD
    cN
    @4
    cmin
    co
    #
    cdvds
    wbr
    #
    @16
    @4
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
    @18
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
    @19
    cz
    wcel
    #
    @27
    cD
    cmul
    co
    #
    @19
    wceq
    @20
    @2
    @26
    @0
    @1
    @26
    cr
    wcel
    #
    @0
    @22
    @1
    cD
    cr
    wcel
    @1
    cD
    cc0
    wne
    @32
    @24
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
    @29
    @0
    cD
    nnz
    #
    adantl
    @0
    @1
    @4
    cz
    wcel
    @30
    @2
    @4
    cN
    cD
    zmodcl
    #
    nn0zd
    cN
    @4
    zsubcl
    syldan
    @2
    cD
    @27
    cmul
    co
    #
    @31
    @19
    @2
    cD
    @27
    @1
    cD
    cc
    wcel
    @0
    cD
    nncn
    adantl
    @2
    @27
    @33
    zcnd
    mulcomd
    @2
    @4
    cN
    @36
    cmin
    co
    #
    wceq
    #
    @36
    @19
    wceq
    #
    @0
    @22
    @23
    @38
    @1
    @24
    @25
    cN
    cD
    modval
    syl2an
    @2
    @37
    @4
    wceq
    #
    @19
    @36
    wceq
    #
    @38
    @39
    @2
    cN
    cc
    wcel
    #
    @36
    cc
    wcel
    @4
    cc
    wcel
    @40
    @41
    wb
    @0
    @42
    @1
    cN
    zcn
    adantr
    @2
    @36
    @0
    @1
    @36
    cz
    wcel
    #
    @1
    @29
    @28
    @43
    @2
    @34
    @33
    cD
    @27
    zmulcl
    syl2an
    anabss7
    zcnd
    @2
    @4
    @35
    nn0cnd
    cN
    @36
    @4
    subsub23
    syl3anc
    @37
    @4
    eqcom
    @19
    @36
    eqcom
    3bitr3g
    mpbid
    eqtr3d
    @27
    cD
    @19
    dvds0lem
    syl31anc
    @2
    @4
    cn0
    wcel
    @10
    vz
    cn0
    wreu
    #
    @18
    @20
    wa
    #
    @21
    wb
    @35
    cD
    cN
    vz
    divalg2
    #
    @10
    @45
    vz
    cn0
    @4
    @6
    @4
    wceq
    #
    @7
    @18
    @9
    @20
    @6
    @4
    cD
    clt
    breq1
    @47
    @8
    @19
    cD
    cdvds
    @6
    @4
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
    @44
    @11
    @17
    wceq
    @46
    @10
    vz
    cn0
    snriota
    syl
    eqtr4d
    eleq2d
    vr
    @4
    velsn
    @10
    @15
    vz
    @3
    cn0
    @6
    @3
    wceq
    #
    @7
    @12
    @9
    @14
    @6
    @3
    cD
    clt
    breq1
    @48
    @8
    @13
    cD
    cdvds
    @6
    @3
    cN
    cmin
    oveq2
    breq2d
    anbi12d
    elrab
    3bitr3g
end
