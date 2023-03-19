include "chil.mm"
include "wcel.mm"
include "cfv.mm"
include "cno.mm"
include "cnop.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c0v.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "csm.mm"
include "cr.mm"
include "cbo.mm"
include "clo.mm"
include "bdopln.mm"
include "ax-mp.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "normcl.mm"
include "syl.mm"
include "adantr.mm"
include "recnd.mm"
include "cc0.mm"
include "normne0.mm"
include "biimpar.mm"
include "divrec2d.mm"
include "cabs.mm"
include "cc.mm"
include "rereccld.mm"
include "simpl.mm"
include "lnopmuli.mm"
include "syl2anc.mm"
include "norm-iii.mm"
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
include "norm1.mm"
include "eqle.mm"
include "wf.mm"
include "nmoplb.mm"
include "mp3an1.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "nmopre.mm"
include "a1i.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "0le0.mm"
include "lnop0i.mm"
include "fveq2i.mm"
include "norm0.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "recni.mm"
include "mul01i.mm"
include "3brtr4i.mm"
include "pm2.61ne.mm"

theorem nmbdoplbi
  let cA: class A
  let cT: class T
  assume nmbdoplb.1: |- T e. BndLinOp


  assert |- ( A e. ~H -> ( normh ` ( T ` A ) ) <_ ( ( normop ` T ) x. ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cno
    cfv
    #
    cT
    cnop
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
    c0v
    cT
    cfv
    #
    cno
    cfv
    #
    @3
    c0v
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
    @2
    @8
    @5
    @10
    cle
    @12
    @1
    @7
    cno
    cA
    c0v
    cT
    fveq2
    fveq2d
    @12
    @4
    @9
    @3
    cmul
    cA
    c0v
    cno
    fveq2
    oveq2d
    breq12d
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
    @14
    @15
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
    cno
    cfv
    #
    @3
    cle
    @14
    @15
    @17
    @2
    cmul
    co
    #
    @20
    @14
    @2
    @4
    @14
    @2
    @0
    @2
    cr
    wcel
    #
    @13
    @0
    @1
    chil
    wcel
    #
    @22
    chil
    chil
    cA
    cT
    cT
    cT
    cbo
    wcel
    #
    cT
    clo
    wcel
    nmbdoplb.1
    cT
    bdopln
    ax-mp
    #
    lnopfi
    #
    ffvelrni
    #
    @1
    normcl
    syl
    adantr
    #
    recnd
    @14
    @4
    @0
    @4
    cr
    wcel
    #
    @13
    cA
    normcl
    adantr
    #
    recnd
    @0
    @4
    cc0
    wne
    @13
    cA
    normne0
    biimpar
    #
    divrec2d
    @14
    @20
    @17
    @1
    csm
    co
    #
    cno
    cfv
    #
    @17
    cabs
    cfv
    #
    @2
    cmul
    co
    #
    @21
    @14
    @19
    @32
    cno
    @14
    @17
    cc
    wcel
    #
    @0
    @19
    @32
    wceq
    @14
    @17
    @14
    @4
    @30
    @31
    rereccld
    #
    recnd
    #
    @0
    @13
    simpl
    #
    @17
    cA
    cT
    @25
    lnopmuli
    syl2anc
    fveq2d
    @14
    @36
    @23
    @33
    @35
    wceq
    @38
    @0
    @23
    @13
    @27
    adantr
    @17
    @1
    norm-iii
    syl2anc
    @14
    @34
    @17
    @2
    cmul
    @14
    @17
    @37
    @14
    @17
    cr
    wcel
    #
    cc0
    @17
    clt
    wbr
    #
    cc0
    @17
    cle
    wbr
    #
    @37
    @14
    @4
    @30
    @0
    @13
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
    @40
    @41
    @42
    wi
    0re
    cc0
    @17
    ltle
    mpan
    sylc
    absidd
    oveq1d
    3eqtrrd
    eqtrd
    @14
    @18
    chil
    wcel
    #
    @18
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @20
    @3
    cle
    wbr
    #
    @14
    @36
    @0
    @45
    @38
    @39
    @17
    cA
    hvmulcl
    syl2anc
    #
    @14
    @46
    cr
    wcel
    #
    @46
    c1
    wceq
    @47
    @14
    @45
    @50
    @49
    @18
    normcl
    syl
    cA
    norm1
    @46
    c1
    eqle
    syl2anc
    chil
    chil
    cT
    wf
    @45
    @47
    @48
    @26
    @18
    cT
    nmoplb
    mp3an1
    syl2anc
    eqbrtrd
    @14
    @22
    @3
    cr
    wcel
    #
    @29
    @43
    @16
    @6
    wb
    @28
    @51
    @14
    @24
    @51
    nmbdoplb.1
    cT
    nmopre
    ax-mp
    #
    a1i
    @30
    @44
    @2
    @3
    @4
    ledivmul2
    syl112anc
    mpbid
    @11
    @0
    cc0
    cc0
    @8
    @10
    cle
    0le0
    @8
    @9
    cc0
    @7
    c0v
    cno
    cT
    @25
    lnop0i
    fveq2i
    norm0
    eqtri
    @10
    @3
    cc0
    cmul
    co
    cc0
    @9
    cc0
    @3
    cmul
    norm0
    oveq2i
    @3
    @3
    @52
    recni
    mul01i
    eqtri
    3brtr4i
    a1i
    pm2.61ne
end
