include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "pythagtriplem12.mm"
include "pythagtriplem14.mm"
include "oveq12d.mm"
include "cc.mm"
include "nncn.mm"
include "3ad2ant3.mm"
include "3ad2ant1.mm"
include "addcld.mm"
include "subcld.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "divdir.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "ppncand.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "syl.mm"
include "3eqtrrd.mm"

theorem pythagtriplem17
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume pythagtriplem15.1: |- M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 )
  assume pythagtriplem15.2: |- N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> C = ( ( M ^ 2 ) + ( N ^ 2 ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    caddc
    co
    cC
    c2
    cexp
    co
    wceq
    #
    cA
    cB
    cgcd
    co
    c1
    wceq
    c2
    cA
    cdvds
    wbr
    wn
    wa
    #
    w3a
    #
    cM
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    cA
    caddc
    co
    #
    cC
    cA
    cmin
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c2
    cC
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cC
    @6
    @9
    @10
    c2
    cdiv
    co
    #
    @11
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @13
    @6
    @7
    @16
    @8
    @17
    caddc
    cA
    cB
    cC
    cM
    pythagtriplem15.1
    pythagtriplem12
    cA
    cB
    cC
    cN
    pythagtriplem15.2
    pythagtriplem14
    oveq12d
    @6
    @10
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @13
    @18
    wceq
    #
    @6
    cC
    cA
    @3
    @4
    cC
    cc
    wcel
    #
    @5
    @2
    @0
    @22
    @1
    cC
    nncn
    3ad2ant3
    3ad2ant1
    #
    @3
    @4
    cA
    cc
    wcel
    #
    @5
    @0
    @1
    @24
    @2
    cA
    nncn
    3ad2ant1
    3ad2ant1
    #
    addcld
    @6
    cC
    cA
    @23
    @25
    subcld
    @19
    @20
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    @21
    2cnne0
    @10
    @11
    c2
    divdir
    mp3an3
    syl2anc
    eqtr4d
    @6
    @12
    @14
    c2
    cdiv
    @6
    @12
    cC
    cC
    caddc
    co
    @14
    @6
    cC
    cA
    cC
    @23
    @25
    @23
    ppncand
    @6
    cC
    @23
    2timesd
    eqtr4d
    oveq1d
    @6
    @22
    @15
    cC
    wceq
    #
    @23
    @22
    @26
    @27
    @28
    2cn
    2ne0
    cC
    c2
    divcan3
    mp3an23
    syl
    3eqtrrd
end
