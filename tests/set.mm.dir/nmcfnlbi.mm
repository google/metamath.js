include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wceq.mm"
include "cfv.mm"
include "cabs.mm"
include "cnmf.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "fveq2.mm"
include "lnfn0i.mm"
include "syl6eq.mm"
include "abs00bd.mm"
include "0le0.mm"
include "norm0.mm"
include "oveq2d.mm"
include "nmcfnexi.mm"
include "recni.mm"
include "mul01i.mm"
include "syl6req.mm"
include "syl5breq.mm"
include "eqbrtrd.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "csm.mm"
include "cr.mm"
include "cc.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "abscld.mm"
include "adantr.mm"
include "recnd.mm"
include "normcl.mm"
include "norm-i.mm"
include "notbid.mm"
include "biimpar.mm"
include "neqned.mm"
include "divrec2d.mm"
include "rereccld.mm"
include "simpl.mm"
include "lnfnmuli.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "clt.mm"
include "wne.mm"
include "df-ne.mm"
include "normgt0.mm"
include "syl5bbr.mm"
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
include "sylan2br.mm"
include "eqle.mm"
include "wf.mm"
include "nmfnlb.mm"
include "mp3an1.mm"
include "wb.mm"
include "a1i.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "pm2.61dan.mm"

theorem nmcfnlbi
  let cA: class A
  let cT: class T
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmcfnex.1: |- T e. LinFn
  assume nmcfnex.2: |- T e. ContFn


  assert |- ( A e. ~H -> ( abs ` ( T ` A ) ) <_ ( ( normfn ` T ) x. ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wceq
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
    @1
    @7
    @0
    @1
    @3
    cc0
    @6
    cle
    @1
    @2
    @1
    @2
    c0v
    cT
    cfv
    cc0
    cA
    c0v
    cT
    fveq2
    cT
    nmcfnex.1
    lnfn0i
    syl6eq
    abs00bd
    @1
    cc0
    cc0
    @6
    cle
    0le0
    @1
    @6
    @4
    cc0
    cmul
    co
    cc0
    @1
    @5
    cc0
    @4
    cmul
    @1
    @5
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
    @4
    @4
    cT
    nmcfnex.1
    nmcfnex.2
    nmcfnexi
    #
    recni
    mul01i
    syl6req
    syl5breq
    eqbrtrd
    adantl
    @0
    @1
    wn
    #
    wa
    #
    @3
    @5
    cdiv
    co
    #
    @4
    cle
    wbr
    #
    @7
    @10
    @11
    c1
    @5
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
    @4
    cle
    @10
    @11
    @13
    @3
    cmul
    co
    #
    @16
    @10
    @3
    @5
    @10
    @3
    @0
    @3
    cr
    wcel
    #
    @9
    @0
    @2
    chil
    cc
    cA
    cT
    cT
    nmcfnex.1
    lnfnfi
    #
    ffvelrni
    #
    abscld
    adantr
    #
    recnd
    @10
    @5
    @0
    @5
    cr
    wcel
    #
    @9
    cA
    normcl
    adantr
    #
    recnd
    @10
    @5
    cc0
    @0
    @5
    cc0
    wceq
    #
    wn
    @9
    @0
    @24
    @1
    cA
    norm-i
    notbid
    biimpar
    neqned
    #
    divrec2d
    @10
    @16
    @13
    @2
    cmul
    co
    #
    cabs
    cfv
    @13
    cabs
    cfv
    #
    @3
    cmul
    co
    @17
    @10
    @15
    @26
    cabs
    @10
    @13
    cc
    wcel
    #
    @0
    @15
    @26
    wceq
    @10
    @13
    @10
    @5
    @23
    @25
    rereccld
    #
    recnd
    #
    @0
    @9
    simpl
    #
    @13
    cA
    cT
    nmcfnex.1
    lnfnmuli
    syl2anc
    fveq2d
    @10
    @13
    @2
    @30
    @0
    @2
    cc
    wcel
    @9
    @20
    adantr
    absmuld
    @10
    @27
    @13
    @3
    cmul
    @10
    @13
    @29
    @10
    @13
    cr
    wcel
    #
    cc0
    @13
    clt
    wbr
    #
    cc0
    @13
    cle
    wbr
    #
    @29
    @10
    @5
    @23
    @0
    @9
    cc0
    @5
    clt
    wbr
    #
    @9
    cA
    c0v
    wne
    #
    @0
    @35
    cA
    c0v
    df-ne
    #
    cA
    normgt0
    syl5bbr
    biimpa
    #
    recgt0d
    cc0
    cr
    wcel
    @32
    @33
    @34
    wi
    0re
    cc0
    @13
    ltle
    mpan
    sylc
    absidd
    oveq1d
    3eqtrrd
    eqtrd
    @10
    @14
    chil
    wcel
    #
    @14
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @16
    @4
    cle
    wbr
    #
    @10
    @28
    @0
    @39
    @30
    @31
    @13
    cA
    hvmulcl
    syl2anc
    #
    @10
    @40
    cr
    wcel
    #
    @40
    c1
    wceq
    #
    @41
    @10
    @39
    @44
    @43
    @14
    normcl
    syl
    @9
    @0
    @36
    @45
    @37
    cA
    norm1
    sylan2br
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
    @19
    @14
    cT
    nmfnlb
    mp3an1
    syl2anc
    eqbrtrd
    @10
    @18
    @4
    cr
    wcel
    #
    @22
    @35
    @12
    @7
    wb
    @21
    @46
    @10
    @8
    a1i
    @23
    @38
    @3
    @4
    @5
    ledivmul2
    syl112anc
    mpbid
    pm2.61dan
end
