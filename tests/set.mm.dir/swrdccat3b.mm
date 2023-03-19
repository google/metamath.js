include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cconcat.mm"
include "cop.mm"
include "csubstr.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "elfzubelfz.mm"
include "adantl.mm"
include "swrdccat3.mm"
include "imp.mm"
include "syl12anc.mm"
include "swrdccat3blem.mm"
include "wn.mm"
include "w3a.mm"
include "iftrue.mm"
include "3ad2ant3.mm"
include "cc.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "pncan2.mm"
include "sylanb.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "iffalse.mm"
include "swrdid.mm"
include "eqtr2d.mm"
include "2if2.mm"
include "eqtr4d.mm"
include "ex.mm"

theorem swrdccat3b
  let cA: class A
  let cB: class B
  let cL: class L
  let cM: class M
  let cV: class V
  let vk: setvar k
  let cN: class N
  assume swrdccatin12.l: |- L = ( # ` A )


  assert |- ( ( A e. Word V /\ B e. Word V ) -> ( M e. ( 0 ... ( L + ( # ` B ) ) ) -> ( ( A ++ B ) substr <. M , ( L + ( # ` B ) ) >. ) = if ( L <_ M , ( B substr <. ( M - L ) , ( # ` B ) >. ) , ( ( A substr <. M , L >. ) ++ B ) ) ) )

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
    wa
    #
    cM
    cc0
    cL
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    cA
    cB
    cconcat
    co
    cM
    @5
    cop
    #
    csubstr
    co
    #
    cL
    cM
    cle
    wbr
    #
    cB
    cM
    cL
    cmin
    co
    #
    @4
    cop
    #
    csubstr
    co
    #
    cA
    cM
    cL
    cop
    csubstr
    co
    #
    cB
    cconcat
    co
    #
    cif
    #
    wceq
    @3
    @7
    wa
    #
    @9
    @5
    cL
    cle
    wbr
    #
    cA
    @8
    csubstr
    co
    #
    @10
    cB
    @11
    @5
    cL
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @14
    cB
    cc0
    @20
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    cif
    #
    @16
    @17
    @3
    @7
    @5
    @6
    wcel
    #
    @9
    @26
    wceq
    #
    @3
    @7
    simpl
    @3
    @7
    simpr
    @7
    @27
    @3
    cM
    cc0
    @5
    elfzubelfz
    adantl
    @3
    @7
    @27
    wa
    @28
    cA
    cB
    cL
    cM
    @5
    cV
    swrdccatin12.l
    swrdccat3
    imp
    syl12anc
    @17
    @18
    @10
    @19
    @22
    @25
    @16
    cA
    cB
    cL
    cM
    cV
    swrdccatin12.l
    swrdccat3blem
    @17
    @18
    wn
    #
    @10
    w3a
    #
    @16
    @13
    @22
    @10
    @17
    @16
    @13
    wceq
    @29
    @10
    @13
    @15
    iftrue
    3ad2ant3
    @30
    @12
    @21
    cB
    csubstr
    @30
    @4
    @20
    @11
    @17
    @29
    @4
    @20
    wceq
    #
    @10
    @3
    @31
    @7
    @3
    @20
    @4
    @1
    cA
    chash
    cfv
    #
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @20
    @4
    wceq
    #
    @2
    @1
    @32
    cV
    cA
    lencl
    nn0cnd
    @2
    @4
    cV
    cB
    lencl
    nn0cnd
    @33
    cL
    cc
    wcel
    @34
    @35
    @32
    cL
    cc
    cL
    @32
    swrdccatin12.l
    eqcomi
    eleq1i
    cL
    @4
    pncan2
    sylanb
    syl2an
    #
    eqcomd
    adantr
    3ad2ant1
    opeq2d
    oveq2d
    eqtrd
    @17
    @29
    @10
    wn
    #
    w3a
    #
    @16
    @15
    @25
    @37
    @17
    @16
    @15
    wceq
    @29
    @10
    @13
    @15
    iffalse
    3ad2ant3
    @38
    cB
    @24
    @14
    cconcat
    @38
    @24
    cB
    cc0
    @4
    cop
    #
    csubstr
    co
    #
    cB
    @38
    @23
    @39
    cB
    csubstr
    @38
    @20
    @4
    cc0
    @17
    @29
    @35
    @37
    @3
    @35
    @7
    @36
    adantr
    3ad2ant1
    opeq2d
    oveq2d
    @17
    @29
    @40
    cB
    wceq
    #
    @37
    @3
    @41
    @7
    @2
    @41
    @1
    cV
    cB
    swrdid
    adantl
    adantr
    3ad2ant1
    eqtr2d
    oveq2d
    eqtrd
    2if2
    eqtr4d
    ex
end
