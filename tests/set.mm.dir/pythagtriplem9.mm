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
include "csqrt.mm"
include "cfv.mm"
include "pythagtriplem7.mm"
include "cz.mm"
include "cc0.mm"
include "nnz.mm"
include "zaddcl.mm"
include "syl2anr.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "eqeltrd.mm"

theorem pythagtriplem9
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A ) ) -> ( sqrt ` ( C + B ) ) e. NN )

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
    cC
    cB
    caddc
    co
    #
    csqrt
    cfv
    @7
    cA
    cgcd
    co
    #
    cn
    cA
    cB
    cC
    pythagtriplem7
    @6
    @7
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @7
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
    cn
    wcel
    @3
    @4
    @9
    @5
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
    zaddcl
    syl2anr
    3adant1
    3ad2ant1
    @3
    @4
    @10
    @5
    @0
    @1
    @10
    @2
    cA
    nnz
    3ad2ant1
    3ad2ant1
    @3
    @4
    @13
    @5
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
    3ad2ant1
    @7
    cA
    gcdn0cl
    syl21anc
    eqeltrd
end
