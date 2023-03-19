include "cnr.mm"
include "wcel.mm"
include "wa.mm"
include "c0r.mm"
include "cop.mm"
include "cmul.mm"
include "co.mm"
include "cmr.mm"
include "cm1r.mm"
include "cplr.mm"
include "wceq.mm"
include "0r.mm"
include "mulcnsr.mm"
include "an4s.mm"
include "mpanr12.mm"
include "00sr.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "m1r.mm"
include "eqtri.mm"
include "mulclsr.mm"
include "0idsr.mm"
include "syl.mm"
include "syl5eq.mm"
include "mulcomsr.mm"
include "oveqan12rd.mm"
include "syl6eq.mm"
include "opeq12d.mm"
include "eqtrd.mm"

theorem mulresr
  let cA: class A
  let cB: class B


  assert |- ( ( A e. R. /\ B e. R. ) -> ( <. A , 0R >. x. <. B , 0R >. ) = <. ( A .R B ) , 0R >. )

  proof
    cA
    cnr
    wcel
    #
    cB
    cnr
    wcel
    #
    wa
    #
    cA
    c0r
    cop
    cB
    c0r
    cop
    cmul
    co
    #
    cA
    cB
    cmr
    co
    #
    cm1r
    c0r
    c0r
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    c0r
    cB
    cmr
    co
    #
    cA
    c0r
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    @4
    c0r
    cop
    @2
    c0r
    cnr
    wcel
    #
    @12
    @3
    @11
    wceq
    #
    0r
    0r
    @0
    @12
    @1
    @12
    @13
    cA
    c0r
    cB
    c0r
    mulcnsr
    an4s
    mpanr12
    @2
    @7
    @4
    @10
    c0r
    @2
    @7
    @4
    c0r
    cplr
    co
    #
    @4
    @6
    c0r
    @4
    cplr
    @6
    cm1r
    c0r
    cmr
    co
    #
    c0r
    @5
    c0r
    cm1r
    cmr
    @12
    @5
    c0r
    wceq
    0r
    c0r
    00sr
    ax-mp
    oveq2i
    cm1r
    cnr
    wcel
    @15
    c0r
    wceq
    m1r
    cm1r
    00sr
    ax-mp
    eqtri
    oveq2i
    @2
    @4
    cnr
    wcel
    @14
    @4
    wceq
    cA
    cB
    mulclsr
    @4
    0idsr
    syl
    syl5eq
    @2
    @10
    c0r
    c0r
    cplr
    co
    #
    c0r
    @1
    @0
    @8
    c0r
    @9
    c0r
    cplr
    @1
    @8
    cB
    c0r
    cmr
    co
    c0r
    c0r
    cB
    mulcomsr
    cB
    00sr
    syl5eq
    cA
    00sr
    oveqan12rd
    @12
    @16
    c0r
    wceq
    0r
    c0r
    0idsr
    ax-mp
    syl6eq
    opeq12d
    eqtrd
end
