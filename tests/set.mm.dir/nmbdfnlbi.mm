include "chil.mm"
include "wcel.mm"
include "cfv.mm"
include "cabs.mm"
include "cnmf.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c0v.mm"
include "wceq.mm"
include "cc0.mm"
include "fveq2.mm"
include "clf.mm"
include "cr.mm"
include "simpli.mm"
include "lnfn0i.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "0le0.mm"
include "norm0.mm"
include "oveq2d.mm"
include "simpri.mm"
include "recni.mm"
include "mul01i.mm"
include "syl6req.mm"
include "syl5breq.mm"
include "eqbrtrd.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "csm.mm"
include "cc.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "abscld.mm"
include "adantr.mm"
include "recnd.mm"
include "normcl.mm"
include "normne0.mm"
include "biimpar.mm"
include "divrec2d.mm"
include "rereccld.mm"
include "simpl.mm"
include "lnfnmuli.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "clt.mm"
include "normgt0.mm"
include "biimpa.mm"
include "recgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "absidd.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"
include "hvmulcl.mm"
include "syl.mm"
include "norm1.mm"
include "eqle.mm"
include "wf.mm"
include "nmfnlb.mm"
include "mp3an1.mm"
include "wb.mm"
include "a1i.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "pm2.61dane.mm"

theorem nmbdfnlbi
  let cA: class A
  let cT: class T
  assume nmbdfnlb.1: |- ( T e. LinFn /\ ( normfn ` T ) e. RR )


  assert |- ( A e. ~H -> ( abs ` ( T ` A ) ) <_ ( ( normfn ` T ) x. ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cabs
    cfv
    #
    cT
    cnmf
    cfv
    #
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cA
    c0v
    cA
    c0v
    wceq
    #
    @6
    @0
    @7
    @2
    cc0
    @5
    cle
    @7
    @1
    @7
    @1
    c0v
    cT
    cfv
    cc0
    cA
    c0v
    cT
    fveq2
    cT
    cT
    clf
    wcel
    #
    @3
    cr
    wcel
    #
    nmbdfnlb.1
    simpli
    #
    lnfn0i
    syl6eq
    abs00bd
    @7
    cc0
    cc0
    @5
    cle
    0le0
    @7
    @5
    @3
    cc0
    cmul
    co
    cc0
    @7
    @4
    cc0
    @3
    cmul
    @7
    @4
    c0v
    cno
    cfv
    cc0
    cA
    c0v
    cno
    fveq2
    norm0
    syl6eq
    oveq2d
    @3
    @3
    @8
    @9
    nmbdfnlb.1
    simpri
    #
    recni
    mul01i
    syl6req
    syl5breq
    eqbrtrd
    adantl
    @0
    cA
    c0v
    wne
    #
    wa
    #
    @2
    @4
    cdiv
    co
    #
    @3
    cle
    wbr
    #
    @6
    @13
    @14
    c1
    @4
    cdiv
    co
    #
    cA
    csm
    co
    #
    cT
    cfv
    #
    cabs
    cfv
    #
    @3
    cle
    @13
    @14
    @16
    @2
    cmul
    co
    #
    @19
    @13
    @2
    @4
    @13
    @2
    @0
    @2
    cr
    wcel
    #
    @12
    @0
    @1
    chil
    cc
    cA
    cT
    cT
    @10
    lnfnfi
    #
    ffvelrni
    #
    abscld
    adantr
    #
    recnd
    @13
    @4
    @0
    @4
    cr
    wcel
    #
    @12
    cA
    normcl
    adantr
    #
    recnd
    @0
    @4
    cc0
    wne
    @12
    cA
    normne0
    biimpar
    #
    divrec2d
    @13
    @19
    @16
    @1
    cmul
    co
    #
    cabs
    cfv
    @16
    cabs
    cfv
    #
    @2
    cmul
    co
    @20
    @13
    @18
    @28
    cabs
    @13
    @16
    cc
    wcel
    #
    @0
    @18
    @28
    wceq
    @13
    @16
    @13
    @4
    @26
    @27
    rereccld
    #
    recnd
    #
    @0
    @12
    simpl
    #
    @16
    cA
    cT
    @10
    lnfnmuli
    syl2anc
    fveq2d
    @13
    @16
    @1
    @32
    @0
    @1
    cc
    wcel
    @12
    @23
    adantr
    absmuld
    @13
    @29
    @16
    @2
    cmul
    @13
    @16
    @31
    @13
    @16
    cr
    wcel
    #
    cc0
    @16
    clt
    wbr
    #
    cc0
    @16
    cle
    wbr
    #
    @31
    @13
    @4
    @26
    @0
    @12
    cc0
    @4
    clt
    wbr
    #
    cA
    normgt0
    biimpa
    #
    recgt0d
    cc0
    cr
    wcel
    @34
    @35
    @36
    wi
    0re
    cc0
    @16
    ltle
    mpan
    sylc
    absidd
    oveq1d
    3eqtrrd
    eqtrd
    @13
    @17
    chil
    wcel
    #
    @17
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @19
    @3
    cle
    wbr
    #
    @13
    @30
    @0
    @39
    @32
    @33
    @16
    cA
    hvmulcl
    syl2anc
    #
    @13
    @40
    cr
    wcel
    #
    @40
    c1
    wceq
    @41
    @13
    @39
    @44
    @43
    @17
    normcl
    syl
    cA
    norm1
    @40
    c1
    eqle
    syl2anc
    chil
    cc
    cT
    wf
    @39
    @41
    @42
    @22
    @17
    cT
    nmfnlb
    mp3an1
    syl2anc
    eqbrtrd
    @13
    @21
    @9
    @25
    @37
    @15
    @6
    wb
    @24
    @9
    @13
    @11
    a1i
    @26
    @38
    @2
    @3
    @4
    ledivmul2
    syl112anc
    mpbid
    pm2.61dane
end
