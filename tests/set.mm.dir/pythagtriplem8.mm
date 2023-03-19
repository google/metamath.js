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
include "csqrt.mm"
include "cfv.mm"
include "pythagtriplem6.mm"
include "cz.mm"
include "cc0.mm"
include "nnz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "eqeltrd.mm"

theorem pythagtriplem8
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( sqrt ` ( C - B ) ) e. NN )

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
    cC
    cB
    cmin
    co
    #
    csqrt
    cfv
    @6
    cA
    cgcd
    co
    #
    cn
    cA
    cB
    cC
    pythagtriplem6
    @3
    @4
    @7
    cn
    wcel
    #
    @5
    @3
    @6
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @6
    cc0
    wceq
    #
    cA
    cc0
    wceq
    #
    wa
    wn
    #
    @8
    @1
    @2
    @9
    @0
    @2
    cC
    cz
    wcel
    cB
    cz
    wcel
    @9
    @1
    cC
    nnz
    cB
    nnz
    cC
    cB
    zsubcl
    syl2anr
    3adant1
    @0
    @1
    @10
    @2
    cA
    nnz
    3ad2ant1
    @0
    @1
    @13
    @2
    @0
    @12
    @11
    @0
    cA
    cc0
    cA
    nnne0
    neneqd
    intnand
    3ad2ant1
    @6
    cA
    gcdn0cl
    syl21anc
    3ad2ant1
    eqeltrd
end
