include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "cexp.mm"
include "co.mm"
include "cn0.mm"
include "prmnn.mm"
include "ax-mp.mm"
include "nnnn0i.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "a1i.mm"
include "id.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "nncni.mm"
include "mulcomi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "cv.mm"
include "cdvds.mm"
include "cmin.mm"
include "cmo.mm"
include "cdiv.mm"
include "cgcd.mm"
include "wa.mm"
include "cz.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "prmdvdsexpb.mm"
include "mp3an23.mm"
include "eqcomi.mm"
include "nnmulcli.mm"
include "eqeltri.mm"
include "peano2nn.mm"
include "ax-1cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "oveq2i.mm"
include "cr.mm"
include "nnrei.mm"
include "cc0.mm"
include "nngt0i.mm"
include "1re.mm"
include "ltaddpos2.mm"
include "mpbi.mm"
include "breqtrri.mm"
include "1mod.mm"
include "oveq2.mm"
include "3eqtrri.mm"
include "subcli.mm"
include "nnne0i.mm"
include "divmuli.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "nnzi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpan.mm"
include "sylancr.mm"
include "syl6bi.mm"
include "rgen.mm"
include "pockthg.mm"

theorem pockthi
  let cA: class A
  let cD: class D
  let cP: class P
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume pockthi.p: |- P e. Prime
  assume pockthi.g: |- G e. NN
  assume pockthi.m: |- M = ( G x. P )
  assume pockthi.n: |- N = ( M + 1 )
  assume pockthi.d: |- D e. NN
  assume pockthi.e: |- E e. NN
  assume pockthi.a: |- A e. NN
  assume pockthi.fac: |- M = ( D x. ( P ^ E ) )
  assume pockthi.gt: |- D < ( P ^ E )
  assume pockthi.mod: |- ( ( A ^ M ) mod N ) = ( 1 mod N )
  assume pockthi.gcd: |- ( ( ( A ^ G ) - 1 ) gcd N ) = 1


  assert |- N e. Prime

  proof
    cD
    cn
    wcel
    #
    cN
    cprime
    wcel
    pockthi.d
    @0
    vy
    cP
    cE
    cexp
    co
    #
    cD
    cN
    vx
    @1
    cn
    wcel
    #
    @0
    cP
    cn
    wcel
    #
    cE
    cn0
    wcel
    @2
    cP
    cprime
    wcel
    #
    @3
    pockthi.p
    cP
    prmnn
    ax-mp
    #
    cE
    pockthi.e
    nnnn0i
    cP
    cE
    nnexpcl
    mp2an
    #
    a1i
    @0
    id
    cD
    @1
    clt
    wbr
    @0
    pockthi.gt
    a1i
    cN
    @1
    cD
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    @0
    cN
    cM
    c1
    caddc
    co
    #
    @8
    pockthi.n
    cM
    @7
    c1
    caddc
    cM
    cD
    @1
    cmul
    co
    @7
    pockthi.fac
    cD
    @1
    cD
    pockthi.d
    nncni
    @1
    @6
    nncni
    mulcomi
    eqtri
    oveq1i
    eqtri
    a1i
    vx
    cv
    #
    @1
    cdvds
    wbr
    #
    vy
    cv
    #
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cN
    cmo
    co
    #
    c1
    wceq
    #
    @12
    @13
    @10
    cdiv
    co
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    vy
    cz
    wrex
    #
    wi
    #
    vx
    cprime
    wral
    @0
    @24
    vx
    cprime
    @10
    cprime
    wcel
    #
    @11
    @10
    cP
    wceq
    #
    @23
    @25
    @4
    cE
    cn
    wcel
    @11
    @26
    wb
    pockthi.p
    pockthi.e
    @10
    cP
    cE
    prmdvdsexpb
    mp3an23
    @26
    cA
    @13
    cexp
    co
    #
    cN
    cmo
    co
    #
    c1
    wceq
    #
    cA
    @17
    cexp
    co
    #
    c1
    cmin
    co
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @23
    @28
    cA
    cM
    cexp
    co
    #
    cN
    cmo
    co
    #
    c1
    @27
    @34
    cN
    cmo
    @13
    cM
    cA
    cexp
    @13
    cM
    wceq
    @9
    cN
    wceq
    cN
    @9
    pockthi.n
    eqcomi
    cN
    c1
    cM
    cN
    cN
    @9
    cn
    pockthi.n
    cM
    cn
    wcel
    @9
    cn
    wcel
    cM
    cG
    cP
    cmul
    co
    #
    cn
    pockthi.m
    cG
    cP
    pockthi.g
    @5
    nnmulcli
    eqeltri
    #
    cM
    peano2nn
    ax-mp
    eqeltri
    #
    nncni
    #
    ax-1cn
    cM
    @37
    nncni
    subadd2i
    mpbir
    #
    oveq2i
    oveq1i
    @35
    c1
    cN
    cmo
    co
    #
    c1
    pockthi.mod
    cN
    cr
    wcel
    c1
    cN
    clt
    wbr
    @41
    c1
    wceq
    cN
    @38
    nnrei
    c1
    @9
    cN
    clt
    cc0
    cM
    clt
    wbr
    #
    c1
    @9
    clt
    wbr
    #
    cM
    @37
    nngt0i
    cM
    cr
    wcel
    c1
    cr
    wcel
    @42
    @43
    wb
    cM
    @37
    nnrei
    1re
    cM
    c1
    ltaddpos2
    mp2an
    mpbi
    pockthi.n
    breqtrri
    cN
    1mod
    mp2an
    eqtri
    eqtri
    @26
    @32
    cA
    cG
    cexp
    co
    #
    c1
    cmin
    co
    #
    cN
    cgcd
    co
    c1
    @26
    @31
    @45
    cN
    cgcd
    @26
    @30
    @44
    c1
    cmin
    @26
    @17
    cG
    cA
    cexp
    @26
    @17
    @13
    cP
    cdiv
    co
    #
    cG
    @10
    cP
    @13
    cdiv
    oveq2
    @46
    cG
    wceq
    cP
    cG
    cmul
    co
    #
    @13
    wceq
    @13
    cM
    @36
    @47
    @40
    pockthi.m
    cG
    cP
    cG
    pockthi.g
    nncni
    #
    cP
    @5
    nncni
    #
    mulcomi
    3eqtrri
    @13
    cP
    cG
    cN
    c1
    @39
    ax-1cn
    subcli
    @49
    @48
    cP
    @5
    nnne0i
    divmuli
    mpbir
    syl6eq
    oveq2d
    oveq1d
    oveq1d
    pockthi.gcd
    syl6eq
    cA
    cz
    wcel
    @29
    @33
    wa
    #
    @23
    cA
    pockthi.a
    nnzi
    @22
    @50
    vy
    cA
    cz
    @12
    cA
    wceq
    #
    @16
    @29
    @21
    @33
    @51
    @15
    @28
    c1
    @51
    @14
    @27
    cN
    cmo
    @12
    cA
    @13
    cexp
    oveq1
    oveq1d
    eqeq1d
    @51
    @20
    @32
    c1
    @51
    @19
    @31
    cN
    cgcd
    @51
    @18
    @30
    c1
    cmin
    @12
    cA
    @17
    cexp
    oveq1
    oveq1d
    oveq1d
    eqeq1d
    anbi12d
    rspcev
    mpan
    sylancr
    syl6bi
    rgen
    a1i
    pockthg
    ax-mp
end
