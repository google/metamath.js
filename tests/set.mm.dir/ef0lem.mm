include "cc0.mm"
include "wceq.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "cli.mm"
include "csn.mm"
include "cv.mm"
include "cuz.mm"
include "wcel.mm"
include "cn.mm"
include "wo.mm"
include "cif.mm"
include "wa.mm"
include "cn0.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleqr.mm"
include "elnn0.mm"
include "sylib.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "nnnn0.mm"
include "adantl.mm"
include "eftval.mm"
include "syl.mm"
include "oveq1.mm"
include "0exp.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "faccl.mm"
include "nncn.mm"
include "nnne0.mm"
include "div0d.mm"
include "3syl.mm"
include "3eqtrd.mm"
include "wn.mm"
include "wne.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "sylibr.mm"
include "iffalsed.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "0exp0e1.mm"
include "syl6eq.mm"
include "0nn0.mm"
include "ax-mp.mm"
include "fac0.mm"
include "oveq2i.mm"
include "1div1e1.mm"
include "eqtr2i.mm"
include "3eqtr4g.mm"
include "sylan9eqr.mm"
include "iftrued.mm"
include "jaodan.mm"
include "syldan.mm"
include "eleqtri.mm"
include "a1i.mm"
include "1cnd.mm"
include "cfz.mm"
include "wss.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "eqimss2i.mm"
include "fsumcvg2.mm"
include "seq1i.mm"
include "breqtrd.mm"

theorem ef0lem
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let cN: class N
  assume eftval.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint F k
  disjoint N n
  assert |- ( A = 0 -> seq 0 ( + , F ) ~~> 1 )

  proof
    cA
    cc0
    wceq
    #
    caddc
    cF
    cc0
    cseq
    #
    cc0
    @1
    cfv
    c1
    cli
    @0
    cc0
    csn
    #
    c1
    vk
    cF
    cc0
    cc0
    @0
    vk
    cv
    #
    cc0
    cuz
    cfv
    #
    wcel
    #
    @3
    cn
    wcel
    #
    @3
    cc0
    wceq
    #
    wo
    #
    @3
    cF
    cfv
    #
    @3
    @2
    wcel
    #
    c1
    cc0
    cif
    #
    wceq
    #
    @0
    @5
    wa
    #
    @3
    cn0
    wcel
    #
    @8
    @13
    @3
    @4
    cn0
    @0
    @5
    simpr
    nn0uz
    syl6eleqr
    @3
    elnn0
    sylib
    @0
    @6
    @12
    @7
    @0
    @6
    wa
    #
    @9
    cc0
    @11
    @15
    @9
    cA
    @3
    cexp
    co
    #
    @3
    cfa
    cfv
    #
    cdiv
    co
    #
    cc0
    @17
    cdiv
    co
    #
    cc0
    @15
    @14
    @9
    @18
    wceq
    @6
    @14
    @0
    @3
    nnnn0
    adantl
    #
    cA
    vn
    cF
    @3
    eftval.1
    eftval
    syl
    @15
    @16
    cc0
    @17
    cdiv
    @0
    @6
    @16
    cc0
    @3
    cexp
    co
    cc0
    cA
    cc0
    @3
    cexp
    oveq1
    @3
    0exp
    sylan9eq
    oveq1d
    @15
    @14
    @17
    cn
    wcel
    #
    @19
    cc0
    wceq
    @20
    @3
    faccl
    @21
    @17
    @17
    nncn
    @17
    nnne0
    div0d
    3syl
    3eqtrd
    @15
    @10
    c1
    cc0
    @6
    @10
    wn
    #
    @0
    @6
    @3
    cc0
    wne
    @22
    @3
    nnne0
    @10
    @3
    cc0
    vk
    cc0
    velsn
    #
    necon3bbii
    sylibr
    adantl
    iffalsed
    eqtr4d
    @0
    @7
    wa
    #
    @9
    c1
    @11
    @7
    @0
    @9
    cc0
    cF
    cfv
    #
    c1
    @3
    cc0
    cF
    fveq2
    @0
    cA
    cc0
    cexp
    co
    #
    cc0
    cfa
    cfv
    #
    cdiv
    co
    #
    c1
    @27
    cdiv
    co
    #
    @25
    c1
    @0
    @26
    c1
    @27
    cdiv
    @0
    @26
    cc0
    cc0
    cexp
    co
    c1
    cA
    cc0
    cc0
    cexp
    oveq1
    0exp0e1
    syl6eq
    oveq1d
    cc0
    cn0
    wcel
    @25
    @28
    wceq
    0nn0
    cA
    vn
    cF
    cc0
    eftval.1
    eftval
    ax-mp
    @29
    c1
    c1
    cdiv
    co
    c1
    @27
    c1
    c1
    cdiv
    fac0
    oveq2i
    1div1e1
    eqtr2i
    3eqtr4g
    #
    sylan9eqr
    @24
    @10
    c1
    cc0
    @24
    @7
    @10
    @0
    @7
    simpr
    @23
    sylibr
    iftrued
    eqtr4d
    jaodan
    syldan
    cc0
    @4
    wcel
    @0
    cc0
    cn0
    @4
    0nn0
    nn0uz
    eleqtri
    a1i
    @0
    @10
    wa
    1cnd
    @2
    cc0
    cc0
    cfz
    co
    #
    wss
    @0
    @31
    @2
    cc0
    cz
    wcel
    @31
    @2
    wceq
    0z
    cc0
    fzsn
    ax-mp
    eqimss2i
    a1i
    fsumcvg2
    @0
    c1
    caddc
    cF
    cc0
    0z
    @30
    seq1i
    breqtrd
end
