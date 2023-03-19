include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "zmodfz.mm"
include "ancoms.mm"
include "nnz.mm"
include "adantr.mm"
include "simpr.mm"
include "cn0.mm"
include "zmodcl.mm"
include "nn0zd.mm"
include "cdiv.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "moddifz.mm"
include "syl2anr.mm"
include "wne.mm"
include "wb.mm"
include "nnne0.mm"
include "zsubcld.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "congsym.mm"
include "syl22anc.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem congrep
  let cA: class A
  let cN: class N
  let va: setvar a

  disjoint A a
  disjoint N a
  assert |- ( ( A e. NN /\ N e. ZZ ) -> E. a e. ( 0 ... ( A - 1 ) ) A || ( a - N ) )

  proof
    cA
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cA
    cmo
    co
    #
    cc0
    cA
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    cA
    @3
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    va
    cv
    #
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    va
    @4
    wrex
    @1
    @0
    @5
    cN
    cA
    zmodfz
    ancoms
    @2
    cA
    cz
    wcel
    #
    @1
    @3
    cz
    wcel
    cA
    cN
    @3
    cmin
    co
    #
    cdvds
    wbr
    #
    @7
    @0
    @11
    @1
    cA
    nnz
    adantr
    #
    @0
    @1
    simpr
    #
    @2
    @3
    @1
    @0
    @3
    cn0
    wcel
    cN
    cA
    zmodcl
    ancoms
    nn0zd
    #
    @2
    @13
    @12
    cA
    cdiv
    co
    cz
    wcel
    #
    @1
    cN
    cr
    wcel
    cA
    crp
    wcel
    @17
    @0
    cN
    zre
    cA
    nnrp
    cN
    cA
    moddifz
    syl2anr
    @2
    @11
    cA
    cc0
    wne
    #
    @12
    cz
    wcel
    @13
    @17
    wb
    @14
    @0
    @18
    @1
    cA
    nnne0
    adantr
    @2
    cN
    @3
    @15
    @16
    zsubcld
    cA
    @12
    dvdsval2
    syl3anc
    mpbird
    cA
    cN
    @3
    congsym
    syl22anc
    @10
    @7
    va
    @3
    @4
    @8
    @3
    wceq
    @9
    @6
    cA
    cdvds
    @8
    @3
    cN
    cmin
    oveq1
    breq2d
    rspcev
    syl2anc
end
