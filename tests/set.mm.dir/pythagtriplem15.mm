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
include "simp3.mm"
include "simp1.mm"
include "nnaddcld.mm"
include "nncnd.mm"
include "3ad2ant1.mm"
include "cz.mm"
include "nnz.mm"
include "3ad2ant3.mm"
include "zsubcld.mm"
include "zcnd.mm"
include "cc0.mm"
include "wne.mm"
include "2cnne0.mm"
include "divsubdir.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "nncn.mm"
include "pnncand.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "syl.mm"
include "3eqtrrd.mm"

theorem pythagtriplem15
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume pythagtriplem15.1: |- M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 )
  assume pythagtriplem15.2: |- N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 )


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> A = ( ( M ^ 2 ) - ( N ^ 2 ) ) )

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
    cmin
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
    cmin
    co
    #
    c2
    cdiv
    co
    #
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
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
    cmin
    co
    #
    @13
    @6
    @7
    @16
    @8
    @17
    cmin
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
    @3
    @4
    @19
    @5
    @3
    @10
    @3
    cC
    cA
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp1
    nnaddcld
    nncnd
    3ad2ant1
    @3
    @4
    @20
    @5
    @3
    @11
    @3
    cC
    cA
    @2
    @0
    cC
    cz
    wcel
    @1
    cC
    nnz
    3ad2ant3
    @0
    @1
    cA
    cz
    wcel
    @2
    cA
    nnz
    3ad2ant1
    zsubcld
    zcnd
    3ad2ant1
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
    divsubdir
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
    cA
    cA
    caddc
    co
    @14
    @6
    cC
    cA
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
    @24
    @1
    cC
    nncn
    3ad2ant3
    3ad2ant1
    @3
    @4
    cA
    cc
    wcel
    #
    @5
    @0
    @1
    @25
    @2
    cA
    nncn
    3ad2ant1
    3ad2ant1
    #
    @26
    pnncand
    @6
    cA
    @26
    2timesd
    eqtr4d
    oveq1d
    @6
    @25
    @15
    cA
    wceq
    #
    @26
    @25
    @22
    @23
    @27
    2cn
    2ne0
    cA
    c2
    divcan3
    mp3an23
    syl
    3eqtrrd
end
