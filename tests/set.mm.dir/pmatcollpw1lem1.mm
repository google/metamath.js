include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cvv.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "fvexd.mm"
include "cn0.mm"
include "wa.mm"
include "ovexd.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveqd.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "clt.mm"
include "wbr.mm"
include "cco1.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cbs.mm"
include "eqid.mm"
include "simp2.mm"
include "simp3.mm"
include "simp13.mm"
include "matecld.mm"
include "coe1ae0.mm"
include "syl.mm"
include "simpl12.mm"
include "adantr.mm"
include "simpr.mm"
include "3simpc.mm"
include "decpmate.mm"
include "syl31anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "cmgp.mm"
include "ply1moncl.mm"
include "syl2anc.mm"
include "ply10s0.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdv.mm"
include "mpd.mm"
include "mptnn0fsuppd.mm"

theorem pmatcollpw1lem1
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vx: setvar x
  assume pmatcollpw1.p: |- P = ( Poly1 ` R )
  assume pmatcollpw1.c: |- C = ( N Mat P )
  assume pmatcollpw1.b: |- B = ( Base ` C )
  assume pmatcollpw1.m: |- .X. = ( .s ` P )
  assume pmatcollpw1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw1.x: |- X = ( var1 ` R )

  disjoint B n
  disjoint I n
  disjoint J n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint X n
  disjoint .X. n
  disjoint .^ n
  disjoint B s
  disjoint B x
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint I s
  disjoint I x
  disjoint J s
  disjoint J x
  disjoint M s
  disjoint M x
  disjoint N s
  disjoint N x
  disjoint P s
  disjoint P x
  disjoint R s
  disjoint R x
  disjoint X s
  disjoint X x
  disjoint .X. s
  disjoint .X. x
  disjoint .^ s
  disjoint .^ x
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ I e. N /\ J e. N ) -> ( n e. NN0 |-> ( ( I ( M decompPMat n ) J ) .X. ( n .^ X ) ) ) finSupp ( 0g ` P ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
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
    cvv
    cI
    cJ
    cM
    vn
    cv
    #
    cdecpmat
    co
    #
    co
    #
    @7
    cX
    c.ex
    co
    #
    c.xp
    co
    cI
    cJ
    cM
    vx
    cv
    #
    cdecpmat
    co
    #
    co
    #
    @11
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    vn
    cvv
    cP
    c0g
    cfv
    #
    vs
    @6
    cP
    c0g
    fvexd
    @6
    @7
    cn0
    wcel
    wa
    @9
    @10
    c.xp
    ovexd
    @7
    @11
    wceq
    #
    @9
    @13
    @10
    @14
    c.xp
    @17
    @8
    @12
    cI
    cJ
    @7
    @11
    cM
    cdecpmat
    oveq2
    oveqd
    @7
    @11
    cX
    c.ex
    oveq1
    oveq12d
    @6
    vs
    cv
    @11
    clt
    wbr
    #
    @11
    cI
    cJ
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
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
    @18
    @15
    @16
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
    @19
    cP
    cbs
    cfv
    #
    wcel
    @26
    @6
    cC
    cB
    cP
    cI
    cJ
    @30
    cM
    cN
    pmatcollpw1.c
    @30
    eqid
    #
    pmatcollpw1.b
    @3
    @4
    @5
    simp2
    @3
    @4
    @5
    simp3
    @0
    @1
    @2
    @4
    @5
    simp13
    #
    matecld
    @20
    @30
    cP
    cR
    vx
    @19
    @22
    vs
    @20
    eqid
    @31
    pmatcollpw1.p
    @22
    eqid
    #
    coe1ae0
    syl
    @6
    @25
    @29
    vs
    cn0
    @6
    @24
    @28
    vx
    cn0
    @6
    @11
    cn0
    wcel
    #
    wa
    #
    @23
    @27
    @18
    @35
    @23
    @27
    @35
    @23
    wa
    #
    @15
    @22
    @14
    c.xp
    co
    #
    @16
    @36
    @13
    @22
    @14
    c.xp
    @36
    @13
    @21
    @22
    @35
    @13
    @21
    wceq
    #
    @23
    @35
    @1
    @2
    @34
    @4
    @5
    wa
    #
    @38
    @0
    @1
    @2
    @4
    @5
    @34
    simpl12
    #
    @6
    @2
    @34
    @32
    adantr
    @6
    @34
    simpr
    #
    @6
    @39
    @34
    @3
    @4
    @5
    3simpc
    adantr
    cB
    cC
    cP
    cR
    cI
    cJ
    @11
    cM
    cN
    crg
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    decpmate
    syl31anc
    adantr
    @35
    @23
    simpr
    eqtrd
    oveq1d
    @35
    @37
    @16
    wceq
    #
    @23
    @35
    @1
    @14
    @30
    wcel
    #
    @42
    @40
    @35
    @1
    @34
    @43
    @40
    @41
    @30
    @11
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    pmatcollpw1.p
    pmatcollpw1.x
    @44
    eqid
    pmatcollpw1.e
    @31
    ply1moncl
    syl2anc
    @30
    cP
    cR
    c.xp
    @14
    @22
    pmatcollpw1.p
    @31
    pmatcollpw1.m
    @33
    ply10s0
    syl2anc
    adantr
    eqtrd
    ex
    imim2d
    ralimdva
    reximdv
    mpd
    mptnn0fsuppd
end
