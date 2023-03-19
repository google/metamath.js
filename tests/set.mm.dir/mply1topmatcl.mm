include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cco1.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "wceq.mm"
include "mply1topmatval.mm"
include "3adant2.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "simp1.mm"
include "cpl1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "c0g.mm"
include "ccmn.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "nn0ex.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "ply1lmod.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "wf.mm"
include "simpl13.mm"
include "coe1f.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "matecld.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "cmgp.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "lmodvscl.mm"
include "fmptd.mm"
include "mply1topmatcllem.mm"
include "gsumcl.mm"
include "matbas2d.mm"
include "eqeltrd.mm"

theorem mply1topmatcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cI: class I
  let cL: class L
  let cN: class N
  let cO: class O
  let cY: class Y
  let vp: setvar p
  let cV: class V
  assume mply1topmat.a: |- A = ( N Mat R )
  assume mply1topmat.q: |- Q = ( Poly1 ` A )
  assume mply1topmat.l: |- L = ( Base ` Q )
  assume mply1topmat.p: |- P = ( Poly1 ` R )
  assume mply1topmat.m: |- .x. = ( .s ` P )
  assume mply1topmat.e: |- E = ( .g ` ( mulGrp ` P ) )
  assume mply1topmat.y: |- Y = ( var1 ` R )
  assume mply1topmat.i: |- I = ( p e. L |-> ( i e. N , j e. N |-> ( P gsum ( k e. NN0 |-> ( ( i ( ( coe1 ` p ) ` k ) j ) .x. ( k E Y ) ) ) ) ) )
  assume mply1topmatcl.c: |- C = ( N Mat P )
  assume mply1topmatcl.b: |- B = ( Base ` C )

  disjoint N i
  disjoint N j
  disjoint N p
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint E p
  disjoint L p
  disjoint P p
  disjoint Y p
  disjoint O i
  disjoint O j
  disjoint O k
  disjoint O p
  disjoint i k
  disjoint j k
  disjoint k p
  disjoint .x. k
  disjoint .x. p
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint V p
  assert |- ( ( N e. Fin /\ R e. Ring /\ O e. L ) -> ( I ` O ) e. B )

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
    cO
    cI
    cfv
    #
    vi
    vj
    cN
    cN
    cP
    vk
    cn0
    vi
    cv
    #
    vj
    cv
    #
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
    @7
    cY
    cE
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cB
    @0
    @2
    @4
    @15
    wceq
    @1
    cA
    cP
    cQ
    cR
    c.x
    vi
    vj
    vk
    cE
    cI
    cL
    cN
    cO
    cfn
    cY
    vp
    mply1topmat.a
    mply1topmat.q
    mply1topmat.l
    mply1topmat.p
    mply1topmat.m
    mply1topmat.e
    mply1topmat.y
    mply1topmat.i
    mply1topmatval
    3adant2
    @3
    vi
    vj
    cC
    cB
    @14
    cP
    cP
    cbs
    cfv
    #
    cN
    cvv
    mply1topmatcl.c
    @16
    eqid
    #
    mply1topmatcl.b
    @0
    @1
    @2
    simp1
    cP
    cvv
    wcel
    @3
    cP
    cR
    cpl1
    cfv
    cvv
    mply1topmat.p
    cR
    cpl1
    fvex
    eqeltri
    a1i
    @3
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    cn0
    @16
    @13
    cP
    cvv
    cP
    c0g
    cfv
    #
    @17
    @21
    eqid
    @3
    @18
    cP
    ccmn
    wcel
    #
    @19
    @1
    @0
    @22
    @2
    @1
    cP
    crg
    wcel
    #
    @22
    cP
    cR
    mply1topmat.p
    ply1ring
    #
    cP
    ringcmn
    syl
    3ad2ant2
    3ad2ant1
    cn0
    cvv
    wcel
    @20
    nn0ex
    a1i
    @20
    vk
    cn0
    @12
    @16
    @13
    @20
    @7
    cn0
    wcel
    #
    wa
    #
    cP
    clmod
    wcel
    #
    @10
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @11
    @16
    wcel
    #
    @12
    @16
    wcel
    @20
    @27
    @25
    @3
    @18
    @27
    @19
    @1
    @0
    @27
    @2
    cP
    cR
    mply1topmat.p
    ply1lmod
    3ad2ant2
    3ad2ant1
    adantr
    @26
    @10
    cR
    cbs
    cfv
    #
    @29
    @26
    cA
    cA
    cbs
    cfv
    #
    cR
    @5
    @6
    @31
    @9
    cN
    mply1topmat.a
    @31
    eqid
    @32
    eqid
    #
    @3
    @18
    @19
    @25
    simpl2
    @3
    @18
    @19
    @25
    simpl3
    @26
    cn0
    @32
    @7
    @8
    @26
    @2
    cn0
    @32
    @8
    wf
    @0
    @1
    @2
    @18
    @19
    @25
    simpl13
    @8
    cL
    cQ
    cA
    cO
    @32
    @8
    eqid
    mply1topmat.l
    mply1topmat.q
    @33
    coe1f
    syl
    @20
    @25
    simpr
    #
    ffvelrnd
    matecld
    @20
    @29
    @31
    wceq
    #
    @25
    @3
    @18
    @35
    @19
    @3
    @28
    cR
    cbs
    @1
    @0
    @28
    cR
    wceq
    @2
    @1
    cR
    @28
    cP
    cR
    crg
    mply1topmat.p
    ply1sca
    eqcomd
    3ad2ant2
    fveq2d
    3ad2ant1
    adantr
    eleqtrrd
    @26
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @25
    cY
    @16
    wcel
    #
    @30
    @20
    @37
    @25
    @3
    @18
    @37
    @19
    @3
    @23
    @37
    @1
    @0
    @23
    @2
    @24
    3ad2ant2
    cP
    @36
    @36
    eqid
    #
    ringmgp
    syl
    3ad2ant1
    adantr
    @34
    @20
    @38
    @25
    @3
    @18
    @38
    @19
    @1
    @0
    @38
    @2
    @16
    cP
    cR
    cY
    mply1topmat.y
    mply1topmat.p
    @17
    vr1cl
    3ad2ant2
    3ad2ant1
    adantr
    @16
    cE
    @36
    @7
    cY
    @16
    cP
    @36
    @39
    @17
    mgpbas
    mply1topmat.e
    mulgnn0cl
    syl3anc
    @10
    c.x
    @28
    @29
    @16
    cP
    @11
    @17
    @28
    eqid
    mply1topmat.m
    @29
    eqid
    lmodvscl
    syl3anc
    @13
    eqid
    fmptd
    cA
    cP
    cQ
    cR
    c.x
    vk
    cE
    @5
    @6
    cL
    cN
    cO
    cY
    mply1topmat.a
    mply1topmat.q
    mply1topmat.l
    mply1topmat.p
    mply1topmat.m
    mply1topmat.e
    mply1topmat.y
    mply1topmatcllem
    gsumcl
    matbas2d
    eqeltrd
end
