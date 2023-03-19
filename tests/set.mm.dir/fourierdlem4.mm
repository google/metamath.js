include "cr.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "cioc.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "simpr.mm"
include "adantr.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "a1i.mm"
include "recnd.mm"
include "gtned.mm"
include "subne0d.mm"
include "eqnetrd.mm"
include "redivcld.mm"
include "flcld.mm"
include "zred.mm"
include "remulcld.mm"
include "readdcld.mm"
include "c1.mm"
include "addid1d.mm"
include "eqcomd.mm"
include "subcld.mm"
include "subidd.mm"
include "oveq2d.mm"
include "addsub12d.mm"
include "nncand.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "cc.mm"
include "addsubd.mm"
include "divdird.mm"
include "dividd.mm"
include "fveq2d.mm"
include "eqeltrrd.mm"
include "peano2re.mm"
include "syl.mm"
include "reflcl.mm"
include "crp.mm"
include "posdifd.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "elrpd.mm"
include "flltp1.mm"
include "cz.mm"
include "1zzd.mm"
include "fladdz.mm"
include "syl2anc.mm"
include "ltmul1dd.mm"
include "ltadd2dd.mm"
include "divcan1d.mm"
include "pncan3d.mm"
include "3brtr3d.mm"
include "flle.mm"
include "lemul1d.mm"
include "leadd2dd.mm"
include "breqtrd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "rexrd.mm"
include "elioc2.mm"
include "mpbir3and.mm"
include "fmptd.mm"

theorem fourierdlem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cE: class E
  let vk: setvar k
  assume fourierdlem4.a: |- ( ph -> A e. RR )
  assume fourierdlem4.b: |- ( ph -> B e. RR )
  assume fourierdlem4.altb: |- ( ph -> A < B )
  assume fourierdlem4.t: |- T = ( B - A )
  assume fourierdlem4.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )

  disjoint A x
  disjoint B x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E : RR --> ( A (,] B ) )

  proof
    wph
    vx
    cr
    vx
    cv
    #
    cB
    @0
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cA
    cB
    cioc
    co
    #
    cE
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @5
    @6
    wcel
    #
    @5
    cr
    wcel
    #
    cA
    @5
    clt
    wbr
    #
    @5
    cB
    cle
    wbr
    #
    @8
    @0
    @4
    wph
    @7
    simpr
    #
    @8
    @3
    cT
    @8
    @3
    @8
    @2
    @8
    @1
    cT
    @8
    cB
    @0
    wph
    cB
    cr
    wcel
    #
    @7
    fourierdlem4.b
    adantr
    #
    @13
    resubcld
    #
    wph
    cT
    cr
    wcel
    @7
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem4.t
    wph
    cB
    cA
    fourierdlem4.b
    fourierdlem4.a
    resubcld
    syl5eqel
    #
    adantr
    #
    wph
    cT
    cc0
    wne
    @7
    wph
    cT
    @17
    cc0
    cT
    @17
    wceq
    wph
    fourierdlem4.t
    a1i
    #
    wph
    cB
    cA
    wph
    cB
    fourierdlem4.b
    recnd
    #
    wph
    cA
    fourierdlem4.a
    recnd
    #
    wph
    cA
    cB
    fourierdlem4.a
    fourierdlem4.altb
    gtned
    subne0d
    eqnetrd
    #
    adantr
    #
    redivcld
    #
    flcld
    zred
    #
    @19
    remulcld
    #
    readdcld
    @8
    @0
    cA
    @0
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @0
    @29
    c1
    caddc
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cA
    @5
    clt
    @8
    @30
    @34
    @0
    @8
    @29
    cT
    @8
    @28
    cT
    @8
    cA
    @0
    wph
    cA
    cr
    wcel
    @7
    fourierdlem4.a
    adantr
    #
    @13
    resubcld
    @19
    @24
    redivcld
    #
    @19
    remulcld
    @8
    @4
    @34
    cr
    @8
    @3
    @33
    cT
    cmul
    @8
    @2
    @32
    cfl
    @8
    @2
    @28
    cT
    caddc
    co
    #
    cT
    cdiv
    co
    @29
    cT
    cT
    cdiv
    co
    #
    caddc
    co
    @32
    @8
    @1
    @38
    cT
    cdiv
    @8
    @1
    cA
    cT
    caddc
    co
    #
    @0
    cmin
    co
    @38
    @8
    cB
    @40
    @0
    cmin
    wph
    cB
    @40
    wceq
    @7
    wph
    cB
    cB
    cc0
    caddc
    co
    #
    cB
    @17
    @17
    cmin
    co
    #
    caddc
    co
    #
    @40
    wph
    @41
    cB
    wph
    cB
    @21
    addid1d
    eqcomd
    wph
    cc0
    @42
    cB
    caddc
    wph
    @42
    cc0
    wph
    @17
    wph
    cB
    cA
    @21
    @22
    subcld
    #
    subidd
    eqcomd
    oveq2d
    wph
    @43
    @17
    cB
    @17
    cmin
    co
    #
    caddc
    co
    @17
    cA
    caddc
    co
    #
    @40
    wph
    cB
    @17
    @17
    @21
    @44
    @44
    addsub12d
    wph
    @45
    cA
    @17
    caddc
    wph
    cB
    cA
    @21
    @22
    nncand
    oveq2d
    wph
    @46
    cA
    @17
    caddc
    co
    @40
    wph
    @17
    cA
    @44
    @22
    addcomd
    wph
    @17
    cT
    cA
    caddc
    wph
    cT
    @17
    @20
    eqcomd
    oveq2d
    eqtrd
    3eqtrd
    3eqtrd
    adantr
    oveq1d
    @8
    cA
    cT
    @0
    wph
    cA
    cc
    wcel
    @7
    @22
    adantr
    #
    @8
    cT
    @19
    recnd
    #
    @8
    @0
    @13
    recnd
    #
    addsubd
    eqtrd
    oveq1d
    @8
    @28
    cT
    cT
    @8
    cA
    @0
    @47
    @49
    subcld
    #
    @48
    @48
    @24
    divdird
    @8
    @39
    c1
    @29
    caddc
    wph
    @39
    c1
    wceq
    @7
    wph
    cT
    wph
    cT
    @17
    cc
    fourierdlem4.t
    @44
    syl5eqel
    @23
    dividd
    adantr
    oveq2d
    3eqtrd
    fveq2d
    oveq1d
    #
    @27
    eqeltrrd
    @13
    @8
    @29
    @33
    cT
    @37
    @8
    @32
    cr
    wcel
    #
    @33
    cr
    wcel
    @8
    @29
    cr
    wcel
    #
    @52
    @37
    @29
    peano2re
    syl
    @32
    reflcl
    syl
    wph
    cT
    crp
    wcel
    @7
    wph
    cT
    @18
    wph
    cc0
    @17
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    cc0
    @17
    clt
    wbr
    fourierdlem4.altb
    wph
    cA
    cB
    fourierdlem4.a
    fourierdlem4.b
    posdifd
    mpbid
    @20
    breqtrrd
    elrpd
    adantr
    #
    @8
    @29
    @29
    cfl
    cfv
    c1
    caddc
    co
    #
    @33
    clt
    @8
    @53
    @29
    @55
    clt
    wbr
    @37
    @29
    flltp1
    syl
    @8
    @53
    c1
    cz
    wcel
    @33
    @55
    wceq
    @37
    @8
    1zzd
    @29
    c1
    fladdz
    syl2anc
    breqtrrd
    ltmul1dd
    ltadd2dd
    @8
    @31
    @0
    @28
    caddc
    co
    cA
    @8
    @30
    @28
    @0
    caddc
    @8
    @28
    cT
    @50
    @48
    @24
    divcan1d
    oveq2d
    @8
    @0
    cA
    @49
    @47
    pncan3d
    eqtrd
    @8
    @5
    @35
    @8
    @4
    @34
    @0
    caddc
    @51
    oveq2d
    eqcomd
    3brtr3d
    @8
    @5
    @0
    @2
    cT
    cmul
    co
    #
    caddc
    co
    #
    cB
    cle
    @8
    @4
    @56
    @0
    @27
    @8
    @2
    cT
    @25
    @19
    remulcld
    @13
    @8
    @3
    @2
    cle
    wbr
    #
    @4
    @56
    cle
    wbr
    @8
    @2
    cr
    wcel
    @58
    @25
    @2
    flle
    syl
    @8
    @3
    @2
    cT
    @26
    @25
    @54
    lemul1d
    mpbid
    leadd2dd
    @8
    @57
    @0
    @1
    caddc
    co
    cB
    @8
    @56
    @1
    @0
    caddc
    @8
    @1
    cT
    @8
    @1
    @16
    recnd
    @48
    @24
    divcan1d
    oveq2d
    @8
    @0
    cB
    @49
    wph
    cB
    cc
    wcel
    @7
    @21
    adantr
    pncan3d
    eqtrd
    breqtrd
    @8
    cA
    cxr
    wcel
    @14
    @9
    @10
    @11
    @12
    w3a
    wb
    @8
    cA
    @36
    rexrd
    @15
    cA
    cB
    @5
    elioc2
    syl2anc
    mpbir3and
    fourierdlem4.e
    fmptd
end
