include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cmul.mm"
include "cv.mm"
include "cprime.mm"
include "cmo.mm"
include "co.mm"
include "clgs.mm"
include "cpc.mm"
include "cexp.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "cr.mm"
include "crp.mm"
include "cn0.mm"
include "zmodcl.mm"
include "3adant3.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "simpr.mm"
include "adantr.mm"
include "simpl3.mm"
include "breq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "oddprm.mm"
include "syl.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zred.mm"
include "simpll1.mm"
include "1red.mm"
include "prmnn.mm"
include "ad2antlr.mm"
include "nnrpd.mm"
include "simp2.mm"
include "modabs2.mm"
include "wb.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wi.mm"
include "prmz.mm"
include "nnzd.mm"
include "zsubcld.mm"
include "dvdstr.mm"
include "mp2and.mm"
include "mpbird.mm"
include "modexp.mm"
include "syl221anc.mm"
include "modadd1.mm"
include "oveq1d.mm"
include "lgsval3.mm"
include "3eqtr4d.mm"
include "cc0.mm"
include "lgscl.mm"
include "zcnd.mm"
include "exp0d.mm"
include "eqtr4d.mm"
include "pceq0.mm"
include "biimpar.mm"
include "oveq2d.mm"
include "pm2.61dan.mm"
include "ifeq1da.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqid.mm"
include "lgsval4a.mm"

theorem lgsmod
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p


  assert |- ( ( A e. ZZ /\ N e. NN /\ -. 2 || N ) -> ( ( A mod N ) /L N ) = ( A /L N ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    wn
    #
    w3a
    #
    cN
    cmul
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    cA
    cN
    cmo
    co
    #
    @5
    clgs
    co
    #
    @5
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cN
    cmul
    vn
    cn
    @6
    cA
    @5
    clgs
    co
    #
    @9
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    @7
    cN
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    @4
    cN
    @13
    @19
    @4
    @12
    @18
    cmul
    c1
    @4
    vn
    cn
    @11
    @17
    @4
    @6
    @10
    @16
    c1
    @4
    @6
    wa
    #
    @5
    cN
    cdvds
    wbr
    #
    @10
    @16
    wceq
    @23
    @24
    wa
    #
    @8
    @15
    @9
    cexp
    @25
    @7
    @5
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    @5
    cmo
    co
    #
    c1
    cmin
    co
    #
    cA
    @26
    cexp
    co
    #
    c1
    caddc
    co
    @5
    cmo
    co
    #
    c1
    cmin
    co
    #
    @8
    @15
    @25
    @28
    @31
    c1
    cmin
    @25
    @27
    cr
    wcel
    @30
    cr
    wcel
    c1
    cr
    wcel
    @5
    crp
    wcel
    #
    @27
    @5
    cmo
    co
    @30
    @5
    cmo
    co
    wceq
    #
    @28
    @31
    wceq
    @25
    @27
    @25
    @7
    cz
    wcel
    #
    @26
    cn0
    wcel
    #
    @27
    cz
    wcel
    @4
    @35
    @6
    @24
    @4
    @7
    @0
    @1
    @7
    cn0
    wcel
    @3
    cA
    cN
    zmodcl
    3adant3
    nn0zd
    #
    ad2antrr
    #
    @25
    @26
    @25
    @5
    cprime
    c2
    csn
    cdif
    wcel
    #
    @26
    cn
    wcel
    @25
    @6
    @5
    c2
    wne
    #
    @39
    @23
    @6
    @24
    @4
    @6
    simpr
    #
    adantr
    @23
    @24
    @40
    @23
    @24
    @5
    c2
    @23
    @24
    wn
    #
    @5
    c2
    wceq
    #
    @3
    @0
    @1
    @3
    @6
    simpl3
    @43
    @24
    @2
    @5
    c2
    cN
    cdvds
    breq1
    notbid
    syl5ibrcom
    necon2ad
    imp
    @5
    cprime
    c2
    eldifsn
    sylanbrc
    #
    @5
    oddprm
    syl
    nnnn0d
    #
    @7
    @26
    zexpcl
    syl2anc
    zred
    @25
    @30
    @25
    @0
    @36
    @30
    cz
    wcel
    @0
    @1
    @3
    @6
    @24
    simpll1
    #
    @45
    cA
    @26
    zexpcl
    syl2anc
    zred
    @25
    1red
    @25
    @5
    @6
    @5
    cn
    wcel
    #
    @4
    @24
    @5
    prmnn
    ad2antlr
    #
    nnrpd
    #
    @25
    @35
    @0
    @36
    @33
    @7
    @5
    cmo
    co
    cA
    @5
    cmo
    co
    wceq
    #
    @34
    @38
    @46
    @45
    @49
    @25
    @50
    @5
    @7
    cA
    cmin
    co
    #
    cdvds
    wbr
    #
    @25
    @24
    cN
    @51
    cdvds
    wbr
    #
    @52
    @23
    @24
    simpr
    @25
    @7
    cN
    cmo
    co
    @7
    wceq
    #
    @53
    @25
    cA
    cr
    wcel
    cN
    crp
    wcel
    @54
    @25
    cA
    @46
    zred
    @25
    cN
    @4
    @1
    @6
    @24
    @0
    @1
    @3
    simp2
    #
    ad2antrr
    #
    nnrpd
    cA
    cN
    modabs2
    syl2anc
    @25
    @1
    @35
    @0
    @54
    @53
    wb
    @56
    @38
    @46
    @7
    cA
    cN
    moddvds
    syl3anc
    mpbid
    @25
    @5
    cz
    wcel
    #
    cN
    cz
    wcel
    @51
    cz
    wcel
    @24
    @53
    wa
    @52
    wi
    @6
    @57
    @4
    @24
    @5
    prmz
    #
    ad2antlr
    @25
    cN
    @56
    nnzd
    @25
    @7
    cA
    @38
    @46
    zsubcld
    @5
    cN
    @51
    dvdstr
    syl3anc
    mp2and
    @25
    @47
    @35
    @0
    @50
    @52
    wb
    @48
    @38
    @46
    @7
    cA
    @5
    moddvds
    syl3anc
    mpbird
    @7
    cA
    @26
    @5
    modexp
    syl221anc
    @27
    @30
    c1
    @5
    modadd1
    syl221anc
    oveq1d
    @25
    @35
    @39
    @8
    @29
    wceq
    @38
    @44
    @7
    @5
    lgsval3
    syl2anc
    @25
    @0
    @39
    @15
    @32
    wceq
    @46
    @44
    cA
    @5
    lgsval3
    syl2anc
    3eqtr4d
    oveq1d
    @23
    @42
    wa
    #
    @8
    cc0
    cexp
    co
    #
    @15
    cc0
    cexp
    co
    #
    @10
    @16
    @59
    @60
    c1
    @61
    @59
    @8
    @59
    @8
    @59
    @35
    @57
    @8
    cz
    wcel
    @4
    @35
    @6
    @42
    @37
    ad2antrr
    @6
    @57
    @4
    @42
    @58
    ad2antlr
    #
    @7
    @5
    lgscl
    syl2anc
    zcnd
    exp0d
    @59
    @15
    @59
    @15
    @59
    @0
    @57
    @15
    cz
    wcel
    @0
    @1
    @3
    @6
    @42
    simpll1
    @62
    cA
    @5
    lgscl
    syl2anc
    zcnd
    exp0d
    eqtr4d
    @59
    @9
    cc0
    @8
    cexp
    @23
    @9
    cc0
    wceq
    #
    @42
    @23
    @6
    @1
    @63
    @42
    wb
    @41
    @4
    @1
    @6
    @55
    adantr
    @5
    cN
    pceq0
    syl2anc
    biimpar
    #
    oveq2d
    @59
    @9
    cc0
    @15
    cexp
    @64
    oveq2d
    3eqtr4d
    pm2.61dan
    ifeq1da
    mpteq2dv
    seqeq3d
    fveq1d
    @4
    @35
    @1
    @21
    @14
    wceq
    @37
    @55
    @7
    vn
    @12
    cN
    @12
    eqid
    lgsval4a
    syl2anc
    @0
    @1
    @22
    @20
    wceq
    @3
    cA
    vn
    @18
    cN
    @18
    eqid
    lgsval4a
    3adant3
    3eqtr4d
end
