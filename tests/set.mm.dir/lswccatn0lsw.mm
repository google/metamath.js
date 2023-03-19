include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "clsw.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "lsw.mm"
include "mp1i.mm"
include "caddc.mm"
include "cfzo.mm"
include "wa.mm"
include "ccatlen.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "lencl.mm"
include "nn0zd.mm"
include "3ad2ant1.mm"
include "lennncl.mm"
include "3adant1.mm"
include "simpl.mm"
include "nnz.mm"
include "adantl.mm"
include "zaddcld.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "ltaddrp.mm"
include "syl2an.mm"
include "3jca.mm"
include "syl2anc.mm"
include "fzolb.mm"
include "sylibr.mm"
include "fzoend.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ccatval2.mm"
include "syld3an3.mm"
include "cc.mm"
include "nn0cnd.mm"
include "addcl.mm"
include "1cnd.mm"
include "sub32d.mm"
include "pncan2.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "3ad2ant2.mm"

theorem lswccatn0lsw
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V /\ B =/= (/) ) -> ( lastS ` ( A ++ B ) ) = ( lastS ` B ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cB
    c0
    wne
    #
    w3a
    #
    cA
    cB
    cconcat
    co
    #
    clsw
    cfv
    #
    cB
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cB
    cfv
    #
    cB
    clsw
    cfv
    #
    @4
    @6
    @5
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @5
    cfv
    #
    @9
    @5
    cvv
    wcel
    @6
    @13
    wceq
    @4
    cA
    cB
    cconcat
    ovex
    @5
    cvv
    lsw
    mp1i
    @4
    @13
    @12
    cA
    chash
    cfv
    #
    cmin
    co
    #
    cB
    cfv
    #
    @9
    @1
    @2
    @3
    @12
    @14
    @14
    @7
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    @13
    @16
    wceq
    @4
    @12
    @17
    c1
    cmin
    co
    #
    @18
    @1
    @2
    @12
    @19
    wceq
    @3
    @1
    @2
    wa
    #
    @11
    @17
    c1
    cmin
    cV
    cA
    cB
    ccatlen
    oveq1d
    #
    3adant3
    @4
    @14
    @18
    wcel
    #
    @19
    @18
    wcel
    @4
    @14
    cz
    wcel
    #
    @17
    cz
    wcel
    #
    @14
    @17
    clt
    wbr
    #
    w3a
    #
    @22
    @4
    @23
    @7
    cn
    wcel
    #
    @26
    @1
    @2
    @23
    @3
    @1
    @14
    cV
    cA
    lencl
    #
    nn0zd
    3ad2ant1
    @2
    @3
    @27
    @1
    cV
    cB
    lennncl
    3adant1
    @23
    @27
    wa
    #
    @23
    @24
    @25
    @23
    @27
    simpl
    #
    @29
    @14
    @7
    @30
    @27
    @7
    cz
    wcel
    @23
    @7
    nnz
    adantl
    zaddcld
    @23
    @14
    cr
    wcel
    @7
    crp
    wcel
    @25
    @27
    @14
    zre
    @7
    nnrp
    @14
    @7
    ltaddrp
    syl2an
    3jca
    syl2anc
    @14
    @17
    fzolb
    sylibr
    @14
    @17
    fzoend
    syl
    eqeltrd
    cV
    cA
    cB
    @12
    ccatval2
    syld3an3
    @4
    @15
    @8
    cB
    @1
    @2
    @15
    @8
    wceq
    @3
    @20
    @15
    @19
    @14
    cmin
    co
    #
    @8
    @20
    @12
    @19
    @14
    cmin
    @21
    oveq1d
    @1
    @14
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @31
    @8
    wceq
    @2
    @1
    @14
    @28
    nn0cnd
    @2
    @7
    cV
    cB
    lencl
    nn0cnd
    @32
    @33
    wa
    #
    @31
    @17
    @14
    cmin
    co
    #
    c1
    cmin
    co
    @8
    @34
    @17
    c1
    @14
    @14
    @7
    addcl
    @34
    1cnd
    @32
    @33
    simpl
    sub32d
    @34
    @35
    @7
    c1
    cmin
    @14
    @7
    pncan2
    oveq1d
    eqtrd
    syl2an
    eqtrd
    3adant3
    fveq2d
    eqtrd
    eqtrd
    @2
    @1
    @9
    @10
    wceq
    @3
    @2
    @10
    @9
    cB
    @0
    lsw
    eqcomd
    3ad2ant2
    eqtrd
end
