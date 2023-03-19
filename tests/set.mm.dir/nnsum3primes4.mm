include "c2.mm"
include "cn.mm"
include "wcel.mm"
include "c3.mm"
include "cle.mm"
include "wbr.mm"
include "c4.mm"
include "c1.mm"
include "cpr.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cfz.mm"
include "2nn.mm"
include "cop.mm"
include "wf.mm"
include "wne.mm"
include "1ne2.mm"
include "1ex.mm"
include "2ex.mm"
include "fpr.mm"
include "wss.mm"
include "2prm.mm"
include "pm3.2i.mm"
include "prss.mm"
include "mpbi.mm"
include "fss.mm"
include "mpan2.mm"
include "mp2b.mm"
include "prmex.mm"
include "prex.mm"
include "elmap.mm"
include "mpbir.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "caddc.mm"
include "cc.mm"
include "2cn.mm"
include "cvv.mm"
include "fveq2.mm"
include "fvpr1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fvpr2.mm"
include "id.mm"
include "ancri.mm"
include "jctl.mm"
include "a1i.mm"
include "sumpr.mm"
include "2p2e4.mm"
include "eqtr2i.mm"
include "fveq1.mm"
include "sumeq2sdv.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "oveq2.mm"
include "df-2.mm"
include "oveq2i.mm"
include "cz.mm"
include "1z.mm"
include "fzpr.mm"
include "1p1e2.mm"
include "preq2i.mm"
include "eqtri.mm"
include "oveq2d.mm"
include "breq1.mm"
include "sumeq1d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"

theorem nnsum3primes4
  let vf: setvar f
  let vk: setvar k
  let vd: setvar d
  let vx: setvar x

  disjoint d f
  disjoint d k
  disjoint f k
  disjoint k x
  assert |- E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 3 /\ 4 = sum_ k e. ( 1 ... d ) ( f ` k ) )

  proof
    c2
    cn
    wcel
    c2
    c3
    cle
    wbr
    #
    c4
    c1
    c2
    cpr
    #
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @1
    cmap
    co
    #
    wrex
    #
    vd
    cv
    #
    c3
    cle
    wbr
    #
    c4
    c1
    @10
    cfz
    co
    #
    @4
    vk
    csu
    #
    wceq
    #
    wa
    #
    vf
    cprime
    @12
    cmap
    co
    #
    wrex
    #
    vd
    cn
    wrex
    2nn
    c1
    c2
    cop
    c2
    c2
    cop
    cpr
    #
    @8
    wcel
    #
    @0
    c4
    @1
    @2
    @18
    cfv
    #
    vk
    csu
    #
    wceq
    #
    wa
    #
    @9
    @19
    @1
    cprime
    @18
    wf
    #
    c1
    c2
    wne
    #
    @1
    c2
    c2
    cpr
    #
    @18
    wf
    #
    @24
    1ne2
    c1
    c2
    c2
    c2
    1ex
    2ex
    2ex
    2ex
    fpr
    @27
    @26
    cprime
    wss
    #
    @24
    c2
    cprime
    wcel
    #
    @29
    wa
    @28
    @29
    @29
    2prm
    2prm
    pm3.2i
    c2
    c2
    cprime
    2ex
    2ex
    prss
    mpbi
    @1
    @26
    cprime
    @18
    fss
    mpan2
    mp2b
    cprime
    @1
    @18
    prmex
    c1
    c2
    prex
    elmap
    mpbir
    @0
    @22
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    @21
    c2
    c2
    caddc
    co
    #
    c4
    c2
    cc
    wcel
    #
    @21
    @30
    wceq
    2cn
    @31
    c1
    c2
    @20
    c2
    vk
    c2
    cvv
    cc
    @2
    c1
    wceq
    @20
    c1
    @18
    cfv
    #
    c2
    @2
    c1
    @18
    fveq2
    @25
    @32
    c2
    wceq
    1ne2
    c1
    c2
    c2
    c2
    1ex
    2ex
    fvpr1
    ax-mp
    syl6eq
    @2
    c2
    wceq
    @20
    c2
    @18
    cfv
    #
    c2
    @2
    c2
    @18
    fveq2
    @25
    @33
    c2
    wceq
    1ne2
    c1
    c2
    c2
    c2
    2ex
    2ex
    fvpr2
    ax-mp
    syl6eq
    @31
    @31
    @31
    id
    ancri
    @31
    c1
    cvv
    wcel
    1ex
    jctl
    @25
    @31
    1ne2
    a1i
    sumpr
    ax-mp
    2p2e4
    eqtr2i
    pm3.2i
    @7
    @23
    vf
    @18
    @8
    @3
    @18
    wceq
    #
    @6
    @22
    @0
    @34
    @5
    @21
    c4
    @34
    @1
    @4
    @20
    vk
    @2
    @3
    @18
    fveq1
    sumeq2sdv
    eqeq2d
    anbi2d
    rspcev
    mp2an
    @17
    @9
    vd
    c2
    cn
    @10
    c2
    wceq
    #
    @15
    @7
    vf
    @16
    @8
    @35
    @12
    @1
    cprime
    cmap
    @35
    @12
    c1
    c2
    cfz
    co
    #
    @1
    @10
    c2
    c1
    cfz
    oveq2
    @36
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    @1
    c2
    @37
    c1
    cfz
    df-2
    oveq2i
    @38
    c1
    @37
    cpr
    #
    @1
    c1
    cz
    wcel
    @38
    @39
    wceq
    1z
    c1
    fzpr
    ax-mp
    @37
    c2
    c1
    1p1e2
    preq2i
    eqtri
    eqtri
    syl6eq
    #
    oveq2d
    @35
    @11
    @0
    @14
    @6
    @10
    c2
    c3
    cle
    breq1
    @35
    @13
    @5
    c4
    @35
    @12
    @1
    @4
    vk
    @40
    sumeq1d
    eqeq2d
    anbi12d
    rexeqbidv
    rspcev
    mp2an
end
