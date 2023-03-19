include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "wcel.mm"
include "cmin.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cprime.mm"
include "cz.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "simpr.mm"
include "2sqlem3.mm"
include "cneg.mm"
include "znegcld.mm"
include "cc.mm"
include "zcnd.mm"
include "sqneg.mm"
include "syl.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "mulneg1d.mm"
include "oveq2d.mm"
include "zmulcld.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "biimpar.mm"
include "wo.mm"
include "prmz.mm"
include "zsqcl.mm"
include "nnzd.mm"
include "zsubcld.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "sqcld.mm"
include "pnpcand.mm"
include "sqmuld.mm"
include "oveq12d.mm"
include "adddid.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "eqtr3d.mm"
include "mul12d.mm"
include "adddird.mm"
include "subdid.mm"
include "subsq.mm"
include "breqtrd.mm"
include "wb.mm"
include "zaddcld.mm"
include "euclemma.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "mpjaodan.mm"

theorem 2sqlem4
  let wph: wff ph
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vu: setvar u
  let vv: setvar v
  let cM: class M
  let cE: class E
  let cY: class Y
  let cF: class F
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )
  assume 2sqlem5.1: |- ( ph -> N e. NN )
  assume 2sqlem5.2: |- ( ph -> P e. Prime )
  assume 2sqlem4.3: |- ( ph -> A e. ZZ )
  assume 2sqlem4.4: |- ( ph -> B e. ZZ )
  assume 2sqlem4.5: |- ( ph -> C e. ZZ )
  assume 2sqlem4.6: |- ( ph -> D e. ZZ )
  assume 2sqlem4.7: |- ( ph -> ( N x. P ) = ( ( A ^ 2 ) + ( B ^ 2 ) ) )
  assume 2sqlem4.8: |- ( ph -> P = ( ( C ^ 2 ) + ( D ^ 2 ) ) )


  assert |- ( ph -> N e. S )

  proof
    wph
    cP
    cC
    cB
    cmul
    co
    #
    cA
    cD
    cmul
    co
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    cN
    cS
    wcel
    cP
    @0
    @1
    cmin
    co
    #
    cdvds
    wbr
    #
    wph
    @3
    wa
    vw
    cA
    cB
    cC
    cD
    cP
    cS
    cN
    2sq.1
    wph
    cN
    cn
    wcel
    #
    @3
    2sqlem5.1
    adantr
    wph
    cP
    cprime
    wcel
    #
    @3
    2sqlem5.2
    adantr
    wph
    cA
    cz
    wcel
    #
    @3
    2sqlem4.3
    adantr
    wph
    cB
    cz
    wcel
    #
    @3
    2sqlem4.4
    adantr
    wph
    cC
    cz
    wcel
    #
    @3
    2sqlem4.5
    adantr
    wph
    cD
    cz
    wcel
    #
    @3
    2sqlem4.6
    adantr
    wph
    cN
    cP
    cmul
    co
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    @3
    2sqlem4.7
    adantr
    wph
    cP
    cC
    c2
    cexp
    co
    #
    cD
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    @3
    2sqlem4.8
    adantr
    wph
    @3
    simpr
    2sqlem3
    wph
    @5
    wa
    vw
    cA
    cneg
    #
    cB
    cC
    cD
    cP
    cS
    cN
    2sq.1
    wph
    @6
    @5
    2sqlem5.1
    adantr
    wph
    @7
    @5
    2sqlem5.2
    adantr
    wph
    @20
    cz
    wcel
    @5
    wph
    cA
    2sqlem4.3
    znegcld
    adantr
    wph
    @9
    @5
    2sqlem4.4
    adantr
    wph
    @10
    @5
    2sqlem4.5
    adantr
    wph
    @11
    @5
    2sqlem4.6
    adantr
    wph
    @12
    @20
    c2
    cexp
    co
    #
    @14
    caddc
    co
    #
    wceq
    @5
    wph
    @12
    @15
    @22
    2sqlem4.7
    wph
    @21
    @13
    @14
    caddc
    wph
    cA
    cc
    wcel
    @21
    @13
    wceq
    wph
    cA
    2sqlem4.3
    zcnd
    #
    cA
    sqneg
    syl
    oveq1d
    eqtr4d
    adantr
    wph
    @19
    @5
    2sqlem4.8
    adantr
    wph
    cP
    @0
    @20
    cD
    cmul
    co
    #
    caddc
    co
    #
    cdvds
    wbr
    @5
    wph
    @25
    @4
    cP
    cdvds
    wph
    @25
    @0
    @1
    cneg
    #
    caddc
    co
    @4
    wph
    @24
    @26
    @0
    caddc
    wph
    cA
    cD
    @23
    wph
    cD
    2sqlem4.6
    zcnd
    #
    mulneg1d
    oveq2d
    wph
    @0
    @1
    wph
    @0
    wph
    cC
    cB
    2sqlem4.5
    2sqlem4.4
    zmulcld
    #
    zcnd
    #
    wph
    @1
    wph
    cA
    cD
    2sqlem4.3
    2sqlem4.6
    zmulcld
    #
    zcnd
    #
    negsubd
    eqtrd
    breq2d
    biimpar
    2sqlem3
    wph
    cP
    @2
    @4
    cmul
    co
    #
    cdvds
    wbr
    #
    @3
    @5
    wo
    #
    wph
    cP
    cP
    @16
    cN
    cmul
    co
    #
    @13
    cmin
    co
    #
    cmul
    co
    #
    @32
    cdvds
    wph
    cP
    cz
    wcel
    #
    @36
    cz
    wcel
    cP
    @37
    cdvds
    wbr
    wph
    @7
    @38
    2sqlem5.2
    cP
    prmz
    syl
    #
    wph
    @35
    @13
    wph
    @16
    cN
    wph
    @10
    @16
    cz
    wcel
    2sqlem4.5
    cC
    zsqcl
    syl
    #
    wph
    cN
    2sqlem5.1
    nnzd
    zmulcld
    #
    wph
    @8
    @13
    cz
    wcel
    2sqlem4.3
    cA
    zsqcl
    syl
    #
    zsubcld
    cP
    @36
    dvdsmul1
    syl2anc
    wph
    @0
    c2
    cexp
    co
    #
    @1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @37
    @32
    wph
    cC
    cA
    cmul
    co
    #
    c2
    cexp
    co
    #
    @43
    caddc
    co
    #
    @47
    @44
    caddc
    co
    #
    cmin
    co
    #
    @45
    @37
    wph
    @47
    @43
    @44
    wph
    @46
    wph
    @46
    wph
    cC
    cA
    2sqlem4.5
    2sqlem4.3
    zmulcld
    zcnd
    sqcld
    wph
    @0
    @29
    sqcld
    wph
    @1
    @31
    sqcld
    pnpcand
    wph
    @50
    cP
    @35
    cmul
    co
    #
    cP
    @13
    cmul
    co
    #
    cmin
    co
    @37
    wph
    @48
    @51
    @49
    @52
    cmin
    wph
    @48
    @16
    @15
    cmul
    co
    #
    @51
    wph
    @48
    @16
    @13
    cmul
    co
    #
    @16
    @14
    cmul
    co
    #
    caddc
    co
    @53
    wph
    @47
    @54
    @43
    @55
    caddc
    wph
    cC
    cA
    wph
    cC
    2sqlem4.5
    zcnd
    #
    @23
    sqmuld
    #
    wph
    cC
    cB
    @56
    wph
    cB
    2sqlem4.4
    zcnd
    #
    sqmuld
    oveq12d
    wph
    @16
    @13
    @14
    wph
    cC
    @56
    sqcld
    #
    wph
    @13
    @42
    zcnd
    #
    wph
    cB
    @58
    sqcld
    adddid
    eqtr4d
    wph
    @53
    @16
    cP
    cN
    cmul
    co
    #
    cmul
    co
    @51
    wph
    @15
    @61
    @16
    cmul
    wph
    @12
    @15
    @61
    2sqlem4.7
    wph
    cN
    cP
    wph
    cN
    2sqlem5.1
    nncnd
    #
    wph
    cP
    @39
    zcnd
    #
    mulcomd
    eqtr3d
    oveq2d
    wph
    @16
    cP
    cN
    @59
    @63
    @62
    mul12d
    eqtrd
    eqtrd
    wph
    @49
    @18
    @13
    cmul
    co
    #
    @52
    wph
    @49
    @54
    @17
    @13
    cmul
    co
    #
    caddc
    co
    @64
    wph
    @47
    @54
    @44
    @65
    caddc
    @57
    wph
    @44
    @13
    @17
    cmul
    co
    @65
    wph
    cA
    cD
    @23
    @27
    sqmuld
    wph
    @13
    @17
    @60
    wph
    cD
    @27
    sqcld
    #
    mulcomd
    eqtrd
    oveq12d
    wph
    @16
    @17
    @13
    wph
    @16
    @40
    zcnd
    @66
    @60
    adddird
    eqtr4d
    wph
    cP
    @18
    @13
    cmul
    2sqlem4.8
    oveq1d
    eqtr4d
    oveq12d
    wph
    cP
    @35
    @13
    @63
    wph
    @35
    @41
    zcnd
    @60
    subdid
    eqtr4d
    eqtr3d
    wph
    @0
    cc
    wcel
    @1
    cc
    wcel
    @45
    @32
    wceq
    @29
    @31
    @0
    @1
    subsq
    syl2anc
    eqtr3d
    breqtrd
    wph
    @7
    @2
    cz
    wcel
    @4
    cz
    wcel
    @33
    @34
    wb
    2sqlem5.2
    wph
    @0
    @1
    @28
    @30
    zaddcld
    wph
    @0
    @1
    @28
    @30
    zsubcld
    cP
    @2
    @4
    euclemma
    syl3anc
    mpbid
    mpjaodan
end
