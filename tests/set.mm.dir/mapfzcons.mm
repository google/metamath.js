include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "w3a.mm"
include "caddc.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simp2.mm"
include "cvv.mm"
include "wb.mm"
include "elmapex.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbid.mm"
include "wf1o.mm"
include "simp3.mm"
include "f1osng.mm"
include "sylancr.mm"
include "f1of.mm"
include "syl.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant3.mm"
include "fssd.mm"
include "fzp1disj.mm"
include "a1i.mm"
include "fun.mm"
include "syl21anc.mm"
include "cz.mm"
include "cmin.mm"
include "cuz.mm"
include "cfv.mm"
include "1z.mm"
include "simp1.mm"
include "cc0.mm"
include "nn0uz.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "fzsuc2.mm"
include "eqcomd.mm"
include "unidm.mm"
include "feq23d.mm"
include "mpbird.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "uneq2i.mm"
include "oveq2i.mm"
include "3eltr4g.mm"

theorem mapfzcons
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume mapfzcons.1: |- M = ( N + 1 )


  assert |- ( ( N e. NN0 /\ A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> ( A u. { <. M , C >. } ) e. ( B ^m ( 1 ... M ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cB
    c1
    cN
    cfz
    co
    #
    cmap
    co
    wcel
    #
    cC
    cB
    wcel
    #
    w3a
    #
    cA
    cN
    c1
    caddc
    co
    #
    cC
    cop
    #
    csn
    #
    cun
    #
    cB
    c1
    @5
    cfz
    co
    #
    cmap
    co
    #
    cA
    cM
    cC
    cop
    #
    csn
    #
    cun
    cB
    c1
    cM
    cfz
    co
    #
    cmap
    co
    @4
    @8
    @10
    wcel
    #
    @9
    cB
    @8
    wf
    #
    @4
    @1
    @5
    csn
    #
    cun
    #
    cB
    cB
    cun
    #
    @8
    wf
    #
    @15
    @4
    @1
    cB
    cA
    wf
    #
    @16
    cB
    @7
    wf
    @1
    @16
    cin
    c0
    wceq
    #
    @19
    @4
    @2
    @20
    @0
    @2
    @3
    simp2
    @4
    cB
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @2
    @20
    wb
    @2
    @0
    @22
    @3
    @2
    @22
    @23
    cA
    cB
    @1
    elmapex
    simpld
    3ad2ant2
    #
    c1
    cN
    cfz
    ovex
    cB
    @1
    cA
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    @4
    @16
    cC
    csn
    #
    cB
    @7
    @4
    @16
    @25
    @7
    wf1o
    #
    @16
    @25
    @7
    wf
    @4
    @5
    cvv
    wcel
    @3
    @26
    cN
    c1
    caddc
    ovex
    @0
    @2
    @3
    simp3
    @5
    cC
    cvv
    cB
    f1osng
    sylancr
    @16
    @25
    @7
    f1of
    syl
    @3
    @0
    @25
    cB
    wss
    @2
    cC
    cB
    snssi
    3ad2ant3
    fssd
    @21
    @4
    c1
    cN
    fzp1disj
    a1i
    @1
    @16
    cB
    cB
    cA
    @7
    fun
    syl21anc
    @4
    @17
    @18
    @9
    cB
    @8
    @4
    @9
    @17
    @4
    c1
    cz
    wcel
    cN
    c1
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    @9
    @17
    wceq
    1z
    @4
    cN
    cn0
    @28
    @0
    @2
    @3
    simp1
    cn0
    cc0
    cuz
    cfv
    @28
    nn0uz
    @27
    cc0
    cuz
    1m1e0
    fveq2i
    eqtr4i
    syl6eleq
    c1
    cN
    fzsuc2
    sylancr
    eqcomd
    @18
    cB
    wceq
    @4
    cB
    unidm
    a1i
    feq23d
    mpbid
    @4
    @22
    @9
    cvv
    wcel
    @14
    @15
    wb
    @24
    c1
    @5
    cfz
    ovex
    cB
    @9
    @8
    cvv
    cvv
    elmapg
    sylancl
    mpbird
    @12
    @7
    cA
    @11
    @6
    cM
    @5
    cC
    mapfzcons.1
    opeq1i
    sneqi
    uneq2i
    @13
    @9
    cB
    cmap
    cM
    @5
    c1
    cfz
    mapfzcons.1
    oveq2i
    oveq2i
    3eltr4g
end
