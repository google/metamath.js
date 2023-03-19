include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "simpl1.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "simpl2.mm"
include "exprec.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "breq12d.mm"
include "cr.mm"
include "wb.mm"
include "rprecred.mm"
include "simpr.mm"
include "reclt1d.mm"
include "mpbid.mm"
include "ltexp2.mm"
include "syl31anc.mm"
include "rpexpcl.mm"
include "syl2anc.mm"
include "ltrecd.mm"
include "3bitr4d.mm"

theorem ltexp2r
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( ( A e. RR+ /\ M e. ZZ /\ N e. ZZ ) /\ A < 1 ) -> ( M < N <-> ( A ^ N ) < ( A ^ M ) ) )

  proof
    cA
    crp
    wcel
    #
    cM
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
    c1
    clt
    wbr
    #
    wa
    #
    c1
    cA
    cdiv
    co
    #
    cM
    cexp
    co
    #
    @6
    cN
    cexp
    co
    #
    clt
    wbr
    #
    c1
    cA
    cM
    cexp
    co
    #
    cdiv
    co
    #
    c1
    cA
    cN
    cexp
    co
    #
    cdiv
    co
    #
    clt
    wbr
    cM
    cN
    clt
    wbr
    #
    @12
    @10
    clt
    wbr
    @5
    @7
    @11
    @8
    @13
    clt
    @5
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @1
    @7
    @11
    wceq
    @5
    cA
    @0
    @1
    @2
    @4
    simpl1
    #
    rpcnd
    #
    @5
    cA
    @17
    rpne0d
    #
    @0
    @1
    @2
    @4
    simpl2
    #
    cA
    cM
    exprec
    syl3anc
    @5
    @15
    @16
    @2
    @8
    @13
    wceq
    @18
    @19
    @0
    @1
    @2
    @4
    simpl3
    #
    cA
    cN
    exprec
    syl3anc
    breq12d
    @5
    @6
    cr
    wcel
    @1
    @2
    c1
    @6
    clt
    wbr
    #
    @14
    @9
    wb
    @5
    cA
    @17
    rprecred
    @20
    @21
    @5
    @4
    @22
    @3
    @4
    simpr
    @5
    cA
    @17
    reclt1d
    mpbid
    @6
    cM
    cN
    ltexp2
    syl31anc
    @5
    @12
    @10
    @5
    @0
    @2
    @12
    crp
    wcel
    @17
    @21
    cA
    cN
    rpexpcl
    syl2anc
    @5
    @0
    @1
    @10
    crp
    wcel
    @17
    @20
    cA
    cM
    rpexpcl
    syl2anc
    ltrecd
    3bitr4d
end
