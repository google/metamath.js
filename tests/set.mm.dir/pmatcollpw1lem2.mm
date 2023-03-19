include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cn0.mm"
include "cco1.mm"
include "cfv.mm"
include "cmgp.mm"
include "cmg.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cdecpmat.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl2.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl3.mm"
include "matecld.mm"
include "ply1coe.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpr.mm"
include "decpmate.mm"
include "syl31anc.mm"
include "eqcomd.mm"
include "eqcomi.mm"
include "oveqi.mm"
include "a1i.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem pmatcollpw1lem2
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let vn: setvar n
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  let cI: class I
  let cJ: class J
  assume pmatcollpw1.p: |- P = ( Poly1 ` R )
  assume pmatcollpw1.c: |- C = ( N Mat P )
  assume pmatcollpw1.b: |- B = ( Base ` C )
  assume pmatcollpw1.m: |- .X. = ( .s ` P )
  assume pmatcollpw1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw1.x: |- X = ( var1 ` R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint X n
  disjoint .X. n
  disjoint .^ n
  disjoint P n
  disjoint a n
  disjoint b n
  disjoint B s
  disjoint B x
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint J n
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
  assert |- ( ( ( N e. Fin /\ R e. Ring /\ M e. B ) /\ ( a e. N /\ b e. N ) ) -> ( a M b ) = ( P gsum ( n e. NN0 |-> ( ( a ( M decompPMat n ) b ) .X. ( n .^ X ) ) ) ) )

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
    va
    cv
    #
    cN
    wcel
    #
    vb
    cv
    #
    cN
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    cM
    co
    #
    cP
    vn
    cn0
    vn
    cv
    #
    @10
    cco1
    cfv
    #
    cfv
    #
    @11
    cX
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    c.xp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vn
    cn0
    @4
    @6
    cM
    @11
    cdecpmat
    co
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
    cmpt
    #
    cgsu
    co
    @9
    @1
    @10
    cP
    cbs
    cfv
    #
    wcel
    @10
    @19
    wceq
    @0
    @1
    @2
    @8
    simpl2
    #
    @9
    cC
    cB
    cP
    @4
    @6
    @24
    cM
    cN
    pmatcollpw1.c
    @24
    eqid
    #
    pmatcollpw1.b
    @3
    @5
    @7
    simprl
    @3
    @5
    @7
    simprr
    @0
    @1
    @2
    @8
    simpl3
    #
    matecld
    @12
    @24
    cP
    cR
    c.xp
    vn
    @15
    @10
    @14
    cX
    pmatcollpw1.p
    pmatcollpw1.x
    @26
    pmatcollpw1.m
    @14
    eqid
    @15
    eqid
    @12
    eqid
    ply1coe
    syl2anc
    @9
    @18
    @23
    cP
    cgsu
    @9
    vn
    cn0
    @17
    @22
    @9
    @11
    cn0
    wcel
    #
    wa
    #
    @13
    @20
    @16
    @21
    c.xp
    @29
    @20
    @13
    @29
    @1
    @2
    @28
    @8
    @20
    @13
    wceq
    @9
    @1
    @28
    @25
    adantr
    @9
    @2
    @28
    @27
    adantr
    @9
    @28
    simpr
    @9
    @8
    @28
    @3
    @8
    simpr
    adantr
    cB
    cC
    cP
    cR
    @4
    @6
    @11
    cM
    cN
    crg
    pmatcollpw1.p
    pmatcollpw1.c
    pmatcollpw1.b
    decpmate
    syl31anc
    eqcomd
    @16
    @21
    wceq
    @29
    @15
    c.ex
    @11
    cX
    c.ex
    @15
    pmatcollpw1.e
    eqcomi
    oveqi
    a1i
    oveq12d
    mpteq2dva
    oveq2d
    eqtrd
end
