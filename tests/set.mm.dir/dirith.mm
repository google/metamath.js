include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "czn.mm"
include "cfv.mm"
include "czrh.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cv.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cen.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "cn0.mm"
include "cbs.mm"
include "wfo.mm"
include "simp1.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "eqid.mm"
include "znzrhfo.mm"
include "fofn.mm"
include "3syl.mm"
include "prmz.mm"
include "adantl.mm"
include "fniniseg.mm"
include "baibd.mm"
include "syl2anc.mm"
include "simp2.mm"
include "zndvds.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "rabbi2dva.mm"
include "cui.mm"
include "simp3.mm"
include "znunit.mm"
include "mpbird.mm"
include "dirith2.mm"
include "eqbrtrrd.mm"

theorem dirith
  let cA: class A
  let cN: class N
  let vp: setvar p

  disjoint A p
  disjoint N p
  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> { p e. Prime | N || ( p - A ) } ~~ NN )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    cprime
    cN
    czn
    cfv
    #
    czrh
    cfv
    #
    ccnv
    cA
    @5
    cfv
    #
    csn
    cima
    #
    cin
    cN
    vp
    cv
    #
    cA
    cmin
    co
    cdvds
    wbr
    #
    vp
    cprime
    crab
    cn
    cen
    @3
    @9
    vp
    cprime
    @7
    @3
    @8
    cprime
    wcel
    #
    wa
    #
    @8
    @7
    wcel
    #
    @8
    @5
    cfv
    @6
    wceq
    #
    @9
    @11
    @5
    cz
    wfn
    #
    @8
    cz
    wcel
    #
    @12
    @13
    wb
    @11
    cN
    cn0
    wcel
    #
    cz
    @4
    cbs
    cfv
    #
    @5
    wfo
    @14
    @3
    @16
    @10
    @3
    cN
    @0
    @1
    @2
    simp1
    #
    nnnn0d
    #
    adantr
    #
    @17
    @5
    cN
    @4
    @4
    eqid
    #
    @17
    eqid
    @5
    eqid
    #
    znzrhfo
    cz
    @17
    @5
    fofn
    3syl
    @10
    @15
    @3
    @8
    prmz
    adantl
    #
    @14
    @12
    @15
    @13
    cz
    @6
    @8
    @5
    fniniseg
    baibd
    syl2anc
    @11
    @16
    @15
    @1
    @13
    @9
    wb
    @20
    @23
    @3
    @1
    @10
    @0
    @1
    @2
    simp2
    #
    adantr
    @8
    cA
    @5
    cN
    @4
    @21
    @22
    zndvds
    syl3anc
    bitrd
    rabbi2dva
    @3
    @6
    @7
    @4
    cui
    cfv
    #
    @5
    cN
    @4
    @21
    @22
    @18
    @25
    eqid
    #
    @3
    @6
    @25
    wcel
    #
    @2
    @0
    @1
    @2
    simp3
    @3
    @16
    @1
    @27
    @2
    wb
    @19
    @24
    cA
    @25
    @5
    cN
    @4
    @21
    @26
    @22
    znunit
    syl2anc
    mpbird
    @7
    eqid
    dirith2
    eqbrtrrd
end
