include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "crg.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "matring.mm"
include "sylan2.mm"
include "ringcmn.mm"
include "3adant3.mm"
include "adantr.mm"
include "fzfid.mm"
include "simpll1.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "elfznn0.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "syl2an.mm"
include "anim2i.mm"
include "simpl.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "simprr.mm"
include "anim1i.mm"
include "m2pmfzmap.mm"
include "syl2anc.mm"
include "matvscl.mm"
include "syl22anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"

theorem m2pmfzgsumcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let vi: setvar i
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vb: setvar b
  assume m2pmfzmap.a: |- A = ( N Mat R )
  assume m2pmfzmap.b: |- B = ( Base ` A )
  assume m2pmfzmap.p: |- P = ( Poly1 ` R )
  assume m2pmfzmap.y: |- Y = ( N Mat P )
  assume m2pmfzmap.t: |- T = ( N matToPolyMat R )
  assume m2pmfzmapfsupp.x: |- X = ( var1 ` R )
  assume m2pmfzmapfsupp.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume m2pmfzgsumcl.m: |- .x. = ( .s ` Y )

  disjoint B i
  disjoint M i
  disjoint N i
  disjoint R i
  disjoint Y i
  disjoint b i
  disjoint i s
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( s e. NN0 /\ b e. ( B ^m ( 0 ... s ) ) ) ) -> ( Y gsum ( i e. ( 0 ... s ) |-> ( ( i .^ X ) .x. ( T ` ( b ` i ) ) ) ) ) e. ( Base ` Y ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cn0
    wcel
    #
    vb
    cv
    #
    cB
    cc0
    @4
    cfz
    co
    #
    cmap
    co
    wcel
    #
    wa
    #
    wa
    #
    cY
    cbs
    cfv
    #
    vi
    cY
    @7
    vi
    cv
    #
    cX
    c.ex
    co
    #
    @12
    @6
    cfv
    cT
    cfv
    #
    c.x
    co
    #
    @11
    eqid
    #
    @3
    cY
    ccmn
    wcel
    #
    @9
    @0
    @1
    @17
    @2
    @0
    @1
    wa
    cY
    crg
    wcel
    #
    @17
    @1
    @0
    cP
    crg
    wcel
    #
    @18
    @1
    cR
    crg
    wcel
    #
    @19
    cR
    crngring
    #
    cP
    cR
    m2pmfzmap.p
    ply1ring
    syl
    #
    cY
    cP
    cN
    m2pmfzmap.y
    matring
    sylan2
    cY
    ringcmn
    syl
    3adant3
    adantr
    @10
    cc0
    @4
    fzfid
    @10
    @15
    @11
    wcel
    #
    vi
    @7
    @10
    @12
    @7
    wcel
    #
    wa
    #
    @0
    @19
    @13
    cP
    cbs
    cfv
    #
    wcel
    #
    @14
    @11
    wcel
    #
    @23
    @0
    @1
    @2
    @9
    @24
    simpll1
    @3
    @19
    @9
    @24
    @1
    @0
    @19
    @2
    @22
    3ad2ant2
    ad2antrr
    @10
    @20
    @12
    cn0
    wcel
    @27
    @24
    @3
    @20
    @9
    @1
    @0
    @20
    @2
    @21
    3ad2ant2
    adantr
    @12
    @4
    elfznn0
    @26
    @12
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    m2pmfzmap.p
    m2pmfzmapfsupp.x
    @29
    eqid
    m2pmfzmapfsupp.e
    @26
    eqid
    #
    ply1moncl
    syl2an
    @25
    @0
    @20
    @5
    w3a
    #
    @8
    @24
    wa
    @28
    @10
    @31
    @24
    @10
    @0
    @20
    wa
    #
    @5
    wa
    @31
    @3
    @32
    @9
    @5
    @0
    @1
    @32
    @2
    @1
    @20
    @0
    @21
    anim2i
    3adant3
    @5
    @8
    simpl
    anim12i
    @0
    @20
    @5
    df-3an
    sylibr
    adantr
    @10
    @8
    @24
    @3
    @5
    @8
    simprr
    anim1i
    cA
    cB
    cP
    cR
    @4
    cT
    @12
    cN
    cY
    vb
    m2pmfzmap.a
    m2pmfzmap.b
    m2pmfzmap.p
    m2pmfzmap.y
    m2pmfzmap.t
    m2pmfzmap
    syl2anc
    cY
    @11
    @13
    cP
    c.x
    @26
    cN
    @14
    @30
    m2pmfzmap.y
    @16
    m2pmfzgsumcl.m
    matvscl
    syl22anc
    ralrimiva
    gsummptcl
end
