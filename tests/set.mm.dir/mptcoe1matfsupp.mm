include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cco1.mm"
include "co.mm"
include "cvv.mm"
include "c0g.mm"
include "fvexd.mm"
include "cn0.mm"
include "wa.mm"
include "eqid.mm"
include "simp2.mm"
include "adantr.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "matecld.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csb.mm"
include "cmap.mm"
include "cfsupp.mm"
include "crab.mm"
include "coe1fsupp.mm"
include "elrabi.mm"
include "3syl.mm"
include "fvex.mm"
include "jctir.mm"
include "coe1sfi.mm"
include "syl.mm"
include "fsuppmapnn0ub.mm"
include "sylc.mm"
include "csbov.mm"
include "csbfv.mm"
include "oveqi.mm"
include "eqtri.mm"
include "a1i.mm"
include "oveq.mm"
include "adantl.mm"
include "cmpt2.mm"
include "mat0op.mm"
include "3adant3.mm"
include "eqidd.mm"
include "ovmpt2d.mm"
include "ad4antr.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "a2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "mptnn0fsupp.mm"

theorem mptcoe1matfsupp
  let cA: class A
  let cQ: class Q
  let cR: class R
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let cL: class L
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let vi: setvar i
  let vj: setvar j
  assume mptcoe1matfsupp.a: |- A = ( N Mat R )
  assume mptcoe1matfsupp.q: |- Q = ( Poly1 ` A )
  assume mptcoe1matfsupp.l: |- L = ( Base ` Q )

  disjoint L k
  disjoint I k
  disjoint J k
  disjoint N k
  disjoint O k
  disjoint R k
  disjoint A c
  disjoint A s
  disjoint A x
  disjoint s x
  disjoint L i
  disjoint L j
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint L s
  disjoint L x
  disjoint k s
  disjoint k x
  disjoint I i
  disjoint I j
  disjoint I s
  disjoint I x
  disjoint J i
  disjoint J j
  disjoint J s
  disjoint J x
  disjoint N i
  disjoint N j
  disjoint N s
  disjoint N x
  disjoint O c
  disjoint O i
  disjoint O j
  disjoint O s
  disjoint O x
  disjoint R i
  disjoint R j
  disjoint R s
  disjoint R x
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ O e. L ) /\ I e. N /\ J e. N ) -> ( k e. NN0 |-> ( I ( ( coe1 ` O ) ` k ) J ) ) finSupp ( 0g ` R ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cO
    cL
    wcel
    #
    w3a
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    w3a
    #
    vx
    cR
    cbs
    cfv
    #
    cI
    cJ
    vk
    cv
    #
    cO
    cco1
    cfv
    #
    cfv
    #
    co
    #
    vk
    cvv
    cR
    c0g
    cfv
    #
    vs
    @6
    cR
    c0g
    fvexd
    #
    @6
    @8
    cn0
    wcel
    #
    wa
    cA
    cA
    cbs
    cfv
    #
    cR
    cI
    cJ
    @7
    @10
    cN
    mptcoe1matfsupp.a
    @7
    eqid
    @15
    eqid
    #
    @6
    @4
    @14
    @3
    @4
    @5
    simp2
    #
    adantr
    @6
    @5
    @14
    @3
    @4
    @5
    simp3
    #
    adantr
    @6
    @2
    @14
    @10
    @15
    wcel
    @3
    @4
    @2
    @5
    @0
    @1
    @2
    simp3
    3ad2ant1
    #
    @9
    cL
    cQ
    cA
    cO
    @15
    @8
    @9
    eqid
    #
    mptcoe1matfsupp.l
    mptcoe1matfsupp.q
    @16
    coe1fvalcl
    sylan
    matecld
    @6
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @22
    @9
    cfv
    #
    cA
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    @23
    vk
    @22
    @11
    csb
    #
    @12
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @6
    @9
    @15
    cn0
    cmap
    co
    #
    wcel
    #
    @25
    cvv
    wcel
    #
    wa
    @9
    @25
    cfsupp
    wbr
    #
    @29
    @6
    @35
    @36
    @6
    @2
    @9
    vc
    cv
    @25
    cfsupp
    wbr
    #
    vc
    @34
    crab
    wcel
    @35
    @19
    @9
    cL
    cQ
    cA
    vc
    cO
    @15
    @25
    @20
    mptcoe1matfsupp.l
    mptcoe1matfsupp.q
    @25
    eqid
    #
    @16
    coe1fsupp
    @38
    vc
    @9
    @34
    elrabi
    3syl
    cA
    c0g
    fvex
    jctir
    @6
    @2
    @37
    @19
    @9
    cL
    cQ
    cA
    cO
    @25
    @20
    mptcoe1matfsupp.l
    mptcoe1matfsupp.q
    @39
    coe1sfi
    syl
    vx
    @15
    vs
    @9
    cvv
    @25
    fsuppmapnn0ub
    sylc
    @6
    @28
    @33
    vs
    cn0
    @6
    @21
    cn0
    wcel
    #
    wa
    #
    @27
    @32
    vx
    cn0
    @41
    @22
    cn0
    wcel
    #
    wa
    #
    @23
    @26
    @31
    @43
    @23
    @26
    @31
    @43
    @23
    wa
    #
    @26
    wa
    #
    @30
    cI
    cJ
    @24
    co
    #
    cI
    cJ
    @25
    co
    #
    @12
    @30
    @46
    wceq
    @45
    @30
    cI
    cJ
    vk
    @22
    @10
    csb
    #
    co
    @46
    vk
    @22
    cI
    cJ
    @10
    csbov
    @48
    @24
    cI
    cJ
    vk
    @22
    @9
    csbfv
    oveqi
    eqtri
    a1i
    @26
    @46
    @47
    wceq
    @44
    cI
    cJ
    @24
    @25
    oveq
    adantl
    @6
    @47
    @12
    wceq
    @40
    @42
    @23
    @26
    @6
    vi
    vj
    cI
    cJ
    cN
    cN
    @12
    @12
    @25
    cvv
    @3
    @4
    @25
    vi
    vj
    cN
    cN
    @12
    cmpt2
    wceq
    #
    @5
    @0
    @1
    @49
    @2
    cA
    cR
    vi
    vj
    cN
    @12
    mptcoe1matfsupp.a
    @12
    eqid
    mat0op
    3adant3
    3ad2ant1
    @6
    vi
    cv
    cI
    wceq
    vj
    cv
    cJ
    wceq
    wa
    wa
    @12
    eqidd
    @17
    @18
    @13
    ovmpt2d
    ad4antr
    3eqtrd
    exp31
    a2d
    ralimdva
    reximdva
    mpd
    mptnn0fsupp
end
