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
include "cc0.mm"
include "0le0.mm"
include "a1i.mm"
include "fveq2.mm"
include "lnop0i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "norm0.mm"
include "oveq2d.mm"
include "nmcopexi.mm"
include "recni.mm"
include "mul01i.mm"
include "3brtr4d.mm"
include "adantl.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "csm.mm"
include "cabs.mm"
include "cr.mm"
include "normcl.mm"
include "adantr.mm"
include "normne0.mm"
include "biimpar.mm"
include "rereccld.mm"
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
include "cc.mm"
include "recnd.mm"
include "simpl.mm"
include "lnopmuli.mm"
include "syl2anc.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "norm-iii.mm"
include "eqtrd.mm"
include "syl.mm"
include "divrec2d.mm"
include "3eqtr4rd.mm"
include "hvmulcl.mm"
include "norm1.mm"
include "eqle.mm"
include "wf.mm"
include "nmoplb.mm"
include "mp3an1.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "pm2.61dane.mm"

theorem nmcoplbi
  let cA: class A
  let cT: class T
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nmcopex.1: |- T e. LinOp
  assume nmcopex.2: |- T e. ContOp


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
    cA
    c0v
    cA
    c0v
    wceq
    #
    @6
    @0
    @7
    cc0
    cc0
    @2
    @5
    cle
    cc0
    cc0
    cle
    wbr
    @7
    0le0
    a1i
    @7
    @2
    c0v
    cno
    cfv
    #
    cc0
    @7
    @1
    c0v
    cno
    @7
    @1
    c0v
    cT
    cfv
    c0v
    cA
    c0v
    cT
    fveq2
    cT
    nmcopex.1
    lnop0i
    syl6eq
    fveq2d
    norm0
    syl6eq
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
    @8
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
    cT
    nmcopex.1
    nmcopex.2
    nmcopexi
    #
    recni
    mul01i
    syl6eq
    3brtr4d
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
    @11
    @12
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
    @11
    @14
    cabs
    cfv
    #
    @2
    cmul
    co
    #
    @14
    @2
    cmul
    co
    @17
    @12
    @11
    @18
    @14
    @2
    cmul
    @11
    @14
    @11
    @4
    @0
    @4
    cr
    wcel
    #
    @10
    cA
    normcl
    adantr
    #
    @0
    @4
    cc0
    wne
    @10
    cA
    normne0
    biimpar
    #
    rereccld
    #
    @11
    @14
    cr
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    cc0
    @14
    cle
    wbr
    #
    @23
    @11
    @4
    @21
    @0
    @10
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
    @24
    @25
    @26
    wi
    0re
    cc0
    @14
    ltle
    mpan
    sylc
    absidd
    oveq1d
    @11
    @17
    @14
    @1
    csm
    co
    #
    cno
    cfv
    #
    @19
    @11
    @16
    @29
    cno
    @11
    @14
    cc
    wcel
    #
    @0
    @16
    @29
    wceq
    @11
    @14
    @23
    recnd
    #
    @0
    @10
    simpl
    #
    @14
    cA
    cT
    nmcopex.1
    lnopmuli
    syl2anc
    fveq2d
    @11
    @31
    @1
    chil
    wcel
    #
    @30
    @19
    wceq
    @32
    @0
    @34
    @10
    chil
    chil
    cA
    cT
    cT
    nmcopex.1
    lnopfi
    #
    ffvelrni
    #
    adantr
    @14
    @1
    norm-iii
    syl2anc
    eqtrd
    @11
    @2
    @4
    @11
    @2
    @0
    @2
    cr
    wcel
    #
    @10
    @0
    @34
    @37
    @36
    @1
    normcl
    syl
    adantr
    #
    recnd
    @11
    @4
    @21
    recnd
    @22
    divrec2d
    3eqtr4rd
    @11
    @15
    chil
    wcel
    #
    @15
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @17
    @3
    cle
    wbr
    #
    @11
    @31
    @0
    @39
    @32
    @33
    @14
    cA
    hvmulcl
    syl2anc
    #
    @11
    @40
    cr
    wcel
    #
    @40
    c1
    wceq
    @41
    @11
    @39
    @44
    @43
    @15
    normcl
    syl
    cA
    norm1
    @40
    c1
    eqle
    syl2anc
    chil
    chil
    cT
    wf
    @39
    @41
    @42
    @35
    @15
    cT
    nmoplb
    mp3an1
    syl2anc
    eqbrtrd
    @11
    @37
    @3
    cr
    wcel
    #
    @20
    @27
    @13
    @6
    wb
    @38
    @45
    @11
    @9
    a1i
    @21
    @28
    @2
    @3
    @4
    ledivmul2
    syl112anc
    mpbid
    pm2.61dane
end
