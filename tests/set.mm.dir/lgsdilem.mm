include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "wceq.mm"
include "wn.mm"
include "cle.mm"
include "simplrr.mm"
include "biantrud.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "simpl2.mm"
include "zred.mm"
include "adantr.mm"
include "ltlen.mm"
include "sylancr.mm"
include "simpl1.mm"
include "renegcld.mm"
include "recnd.mm"
include "mul01d.mm"
include "mulneg1d.mm"
include "breq12d.mm"
include "0red.mm"
include "lt0neg1d.mm"
include "biimpa.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "remulcld.mm"
include "3bitr4d.mm"
include "3bitr2rd.mm"
include "lenlt.mm"
include "bitrd.mm"
include "ifbid.mm"
include "oveq2.mm"
include "neg1mulneg1e1.mm"
include "syl6eq.mm"
include "ax-1cn.mm"
include "mulm1i.mm"
include "ifsb.mm"
include "ifnot.mm"
include "eqtr4i.mm"
include "syl6eqr.mm"
include "iftrue.mm"
include "adantl.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "cc.mm"
include "neg1cn.mm"
include "keepel.mm"
include "mulid2i.mm"
include "biimpar.mm"
include "simplrl.mm"
include "ne0gt0d.mm"
include "breq2d.mm"
include "syl5eq.mm"
include "eqtr2d.mm"
include "pm2.61dan.mm"
include "simpr.mm"
include "biantrurd.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "intnanrd.mm"
include "iffalsed.mm"
include "1t1e1.mm"

theorem lgsdilem
  let cA: class A
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ N e. ZZ ) /\ ( A =/= 0 /\ B =/= 0 ) ) -> if ( ( N < 0 /\ ( A x. B ) < 0 ) , -u 1 , 1 ) = ( if ( ( N < 0 /\ A < 0 ) , -u 1 , 1 ) x. if ( ( N < 0 /\ B < 0 ) , -u 1 , 1 ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    wa
    #
    wa
    #
    cN
    cc0
    clt
    wbr
    #
    @8
    cA
    cB
    cmul
    co
    #
    cc0
    clt
    wbr
    #
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    @8
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    @12
    c1
    cif
    #
    @8
    cB
    cc0
    clt
    wbr
    #
    wa
    #
    @12
    c1
    cif
    #
    cmul
    co
    #
    wceq
    @7
    @8
    wa
    #
    @10
    @12
    c1
    cif
    #
    @14
    @12
    c1
    cif
    #
    @17
    @12
    c1
    cif
    #
    cmul
    co
    #
    @13
    @20
    @7
    @22
    @25
    wceq
    #
    @8
    @7
    @14
    @26
    @7
    @14
    wa
    #
    @22
    @12
    @24
    cmul
    co
    #
    @25
    @27
    @22
    @17
    wn
    #
    @12
    c1
    cif
    #
    @28
    @27
    @10
    @29
    @12
    c1
    @27
    @10
    cc0
    cB
    cle
    wbr
    #
    @29
    @27
    @31
    @31
    @5
    wa
    #
    cc0
    cB
    clt
    wbr
    #
    @10
    @27
    @5
    @31
    @3
    @4
    @5
    @14
    simplrr
    biantrud
    @27
    cc0
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @33
    @32
    wb
    0re
    @7
    @35
    @14
    @7
    cB
    @0
    @1
    @2
    @6
    simpl2
    zred
    #
    adantr
    #
    cc0
    cB
    ltlen
    sylancr
    @27
    cA
    cneg
    #
    cc0
    cmul
    co
    #
    @38
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cc0
    @9
    cneg
    #
    clt
    wbr
    @33
    @10
    @27
    @39
    cc0
    @40
    @42
    clt
    @27
    @38
    @27
    @38
    @27
    cA
    @7
    cA
    cr
    wcel
    #
    @14
    @7
    cA
    @0
    @1
    @2
    @6
    simpl1
    zred
    #
    adantr
    #
    renegcld
    #
    recnd
    mul01d
    @27
    cA
    cB
    @27
    cA
    @45
    recnd
    @27
    cB
    @37
    recnd
    mulneg1d
    breq12d
    @27
    @34
    @35
    @38
    cr
    wcel
    cc0
    @38
    clt
    wbr
    #
    @33
    @41
    wb
    @27
    0red
    @37
    @46
    @7
    @14
    @47
    @7
    cA
    @44
    lt0neg1d
    biimpa
    cc0
    cB
    @38
    ltmul2
    syl112anc
    @27
    @9
    @7
    @9
    cr
    wcel
    @14
    @7
    cA
    cB
    @44
    @36
    remulcld
    adantr
    lt0neg1d
    3bitr4d
    3bitr2rd
    @27
    @34
    @35
    @31
    @29
    wb
    0re
    @37
    cc0
    cB
    lenlt
    sylancr
    bitrd
    ifbid
    @28
    @17
    c1
    @12
    cif
    @30
    @17
    @12
    c1
    @28
    c1
    @12
    @24
    @12
    wceq
    @28
    @12
    @12
    cmul
    co
    c1
    @24
    @12
    @12
    cmul
    oveq2
    neg1mulneg1e1
    syl6eq
    @24
    c1
    wceq
    @28
    @12
    c1
    cmul
    co
    @12
    @24
    c1
    @12
    cmul
    oveq2
    c1
    ax-1cn
    mulm1i
    syl6eq
    ifsb
    @17
    @12
    c1
    ifnot
    eqtr4i
    syl6eqr
    @27
    @23
    @12
    @24
    cmul
    @14
    @23
    @12
    wceq
    @7
    @14
    @12
    c1
    iftrue
    adantl
    oveq1d
    eqtr4d
    @7
    @14
    wn
    #
    wa
    #
    @25
    c1
    @24
    cmul
    co
    #
    @22
    @49
    @23
    c1
    @24
    cmul
    @48
    @23
    c1
    wceq
    @7
    @14
    @12
    c1
    iffalse
    adantl
    oveq1d
    @49
    @50
    @24
    @22
    @24
    @17
    @12
    c1
    cc
    neg1cn
    ax-1cn
    keepel
    mulid2i
    @49
    @17
    @10
    @12
    c1
    @49
    @17
    @9
    cA
    cc0
    cmul
    co
    #
    clt
    wbr
    #
    @10
    @49
    @35
    @34
    @43
    cc0
    cA
    clt
    wbr
    @17
    @52
    wb
    @7
    @35
    @48
    @36
    adantr
    @49
    0red
    @7
    @43
    @48
    @44
    adantr
    #
    @49
    cA
    @53
    @7
    cc0
    cA
    cle
    wbr
    #
    @48
    @7
    @34
    @43
    @54
    @48
    wb
    0re
    @44
    cc0
    cA
    lenlt
    sylancr
    biimpar
    @3
    @4
    @5
    @48
    simplrl
    ne0gt0d
    cB
    cc0
    cA
    ltmul2
    syl112anc
    @49
    @51
    cc0
    @9
    clt
    @49
    cA
    @49
    cA
    @53
    recnd
    mul01d
    breq2d
    bitrd
    ifbid
    syl5eq
    eqtr2d
    pm2.61dan
    adantr
    @21
    @10
    @11
    @12
    c1
    @21
    @8
    @10
    @7
    @8
    simpr
    #
    biantrurd
    ifbid
    @21
    @23
    @16
    @24
    @19
    cmul
    @21
    @14
    @15
    @12
    c1
    @21
    @8
    @14
    @55
    biantrurd
    ifbid
    @21
    @17
    @18
    @12
    c1
    @21
    @8
    @17
    @55
    biantrurd
    ifbid
    oveq12d
    3eqtr3d
    @7
    @8
    wn
    #
    wa
    #
    @13
    c1
    c1
    cmul
    co
    #
    @20
    @57
    @13
    c1
    @58
    @57
    @11
    @12
    c1
    @57
    @8
    @10
    @7
    @56
    simpr
    #
    intnanrd
    iffalsed
    1t1e1
    syl6eqr
    @57
    @16
    c1
    @19
    c1
    cmul
    @57
    @15
    @12
    c1
    @57
    @8
    @14
    @59
    intnanrd
    iffalsed
    @57
    @18
    @12
    c1
    @57
    @8
    @17
    @59
    intnanrd
    iffalsed
    oveq12d
    eqtr4d
    pm2.61dan
end
