include "cz.mm"
include "wcel.mm"
include "c8.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "oveq1d.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "zcn.mm"
include "adantr.mm"
include "adantl.mm"
include "1cnd.mm"
include "8cn.mm"
include "8re.mm"
include "8pos.mm"
include "gt0ne0ii.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "mulsubdivbinom2.mm"
include "syl31anc.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem 2lgsoddprmlem1
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ N = ( ( 8 x. A ) + B ) ) -> ( ( ( N ^ 2 ) - 1 ) / 8 ) = ( ( ( 8 x. ( A ^ 2 ) ) + ( 2 x. ( A x. B ) ) ) + ( ( ( B ^ 2 ) - 1 ) / 8 ) ) )

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
    c8
    cA
    cmul
    co
    cB
    caddc
    co
    #
    wceq
    #
    w3a
    #
    cN
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    @2
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    c8
    cdiv
    co
    #
    c8
    cA
    c2
    cexp
    co
    cmul
    co
    c2
    cA
    cB
    cmul
    co
    cmul
    co
    caddc
    co
    cB
    c2
    cexp
    co
    c1
    cmin
    co
    c8
    cdiv
    co
    caddc
    co
    #
    @4
    @6
    @8
    c8
    cdiv
    @4
    @5
    @7
    c1
    cmin
    @3
    @0
    @5
    @7
    wceq
    @1
    cN
    @2
    c2
    cexp
    oveq1
    3ad2ant3
    oveq1d
    oveq1d
    @0
    @1
    @9
    @10
    wceq
    #
    @3
    @0
    @1
    wa
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    c1
    cc
    wcel
    c8
    cc
    wcel
    #
    c8
    cc0
    wne
    #
    wa
    #
    @11
    @0
    @13
    @1
    cA
    zcn
    adantr
    @1
    @14
    @0
    cB
    zcn
    adantl
    @12
    1cnd
    @17
    @12
    @15
    @16
    8cn
    c8
    8re
    8pos
    gt0ne0ii
    pm3.2i
    a1i
    cA
    cB
    c8
    c1
    mulsubdivbinom2
    syl31anc
    3adant3
    eqtrd
end
