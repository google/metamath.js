include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cvv.mm"
include "cc0.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "c0g.mm"
include "fvexd.mm"
include "cn0.mm"
include "wa.mm"
include "ovexd.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "csb.mm"
include "ply1mulgsumlem2.mm"
include "vex.mm"
include "csbov12g.mm"
include "csbov2g.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "csbied.mm"
include "eqtrd.mm"
include "csbov1g.mm"
include "csbvarg.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ax-mp.mm"
include "csca.mm"
include "ply1sca.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "syl.mm"
include "simpr.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "syl5eq.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "mptnn0fsupp.mm"

theorem ply1mulgsumlem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  assume ply1mulgsum.p: |- P = ( Poly1 ` R )
  assume ply1mulgsum.b: |- B = ( Base ` P )
  assume ply1mulgsum.a: |- A = ( coe1 ` K )
  assume ply1mulgsum.c: |- C = ( coe1 ` L )
  assume ply1mulgsum.x: |- X = ( var1 ` R )
  assume ply1mulgsum.pm: |- .X. = ( .r ` P )
  assume ply1mulgsum.sm: |- .x. = ( .s ` P )
  assume ply1mulgsum.rm: |- .* = ( .r ` R )
  assume ply1mulgsum.m: |- M = ( mulGrp ` P )
  assume ply1mulgsum.e: |- .^ = ( .g ` M )

  disjoint A l
  disjoint B l
  disjoint C l
  disjoint K l
  disjoint L l
  disjoint R l
  disjoint A k
  disjoint B k
  disjoint C k
  disjoint K k
  disjoint L k
  disjoint R k
  disjoint .* k
  disjoint k l
  disjoint X k
  disjoint .^ k
  disjoint .x. k
  disjoint A a
  disjoint A b
  disjoint A n
  disjoint A s
  disjoint a b
  disjoint a n
  disjoint a s
  disjoint b n
  disjoint b s
  disjoint n s
  disjoint B a
  disjoint B b
  disjoint B n
  disjoint B s
  disjoint C a
  disjoint C b
  disjoint C n
  disjoint C s
  disjoint K a
  disjoint K b
  disjoint K n
  disjoint K s
  disjoint L a
  disjoint L b
  disjoint L n
  disjoint L s
  disjoint R a
  disjoint R b
  disjoint R n
  disjoint R s
  disjoint A x
  disjoint A z
  disjoint l n
  disjoint l x
  disjoint l z
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint K x
  disjoint K z
  disjoint L x
  disjoint L z
  disjoint R x
  disjoint R z
  disjoint l s
  disjoint s x
  disjoint s z
  disjoint .* s
  disjoint .* z
  disjoint .* n
  disjoint k n
  disjoint k s
  disjoint P n
  disjoint P s
  disjoint X n
  disjoint X s
  disjoint .^ n
  disjoint .^ s
  disjoint .x. n
  disjoint .x. s
  disjoint k x
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> ( k e. NN0 |-> ( ( R gsum ( l e. ( 0 ... k ) |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) .x. ( k .^ X ) ) ) finSupp ( 0g ` P ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    cL
    cB
    wcel
    #
    w3a
    #
    vn
    cvv
    cR
    vl
    cc0
    vk
    cv
    #
    cfz
    co
    #
    vl
    cv
    #
    cA
    cfv
    #
    @4
    @6
    cmin
    co
    #
    cC
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @4
    cX
    c.ex
    co
    #
    c.x
    co
    #
    vk
    cvv
    cP
    c0g
    cfv
    #
    vs
    @3
    cP
    c0g
    fvexd
    @3
    @4
    cn0
    wcel
    wa
    @12
    @13
    c.x
    ovexd
    @3
    vs
    cv
    #
    vn
    cv
    #
    clt
    wbr
    #
    cR
    vl
    cc0
    @17
    cfz
    co
    #
    @7
    @17
    @6
    cmin
    co
    #
    cC
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    @18
    vk
    @17
    @14
    csb
    #
    @15
    wceq
    #
    wi
    #
    vn
    cn0
    wral
    #
    vs
    cn0
    wrex
    cA
    cB
    cC
    cP
    cR
    c.x
    c.xp
    vn
    c.ex
    c.as
    cK
    cL
    cM
    cX
    vs
    vl
    ply1mulgsum.p
    ply1mulgsum.b
    ply1mulgsum.a
    ply1mulgsum.c
    ply1mulgsum.x
    ply1mulgsum.pm
    ply1mulgsum.sm
    ply1mulgsum.rm
    ply1mulgsum.m
    ply1mulgsum.e
    ply1mulgsumlem2
    @3
    @28
    @32
    vs
    cn0
    @3
    @16
    cn0
    wcel
    #
    wa
    #
    @27
    @31
    vn
    cn0
    @34
    @17
    cn0
    wcel
    #
    wa
    #
    @26
    @30
    @18
    @36
    @26
    @30
    @36
    @26
    wa
    @29
    @24
    @17
    cX
    c.ex
    co
    #
    c.x
    co
    #
    @15
    @17
    cvv
    wcel
    #
    @29
    @38
    wceq
    vn
    vex
    @39
    @29
    vk
    @17
    @12
    csb
    #
    vk
    @17
    @13
    csb
    #
    c.x
    co
    @38
    vk
    @17
    @12
    @13
    c.x
    cvv
    csbov12g
    @39
    @40
    @24
    @41
    @37
    c.x
    @39
    @40
    cR
    vk
    @17
    @11
    csb
    #
    cgsu
    co
    @24
    vk
    @17
    cR
    @11
    cgsu
    cvv
    csbov2g
    @39
    @42
    @23
    cR
    cgsu
    @39
    vk
    @17
    @11
    @23
    cvv
    @39
    id
    @4
    @17
    wceq
    #
    @11
    @23
    wceq
    @39
    @43
    vl
    @5
    @10
    @19
    @22
    @4
    @17
    cc0
    cfz
    oveq2
    @43
    @9
    @21
    @7
    c.as
    @43
    @8
    @20
    cC
    @4
    @17
    @6
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    adantl
    csbied
    oveq2d
    eqtrd
    @39
    @41
    vk
    @17
    @4
    csb
    #
    cX
    c.ex
    co
    @37
    vk
    @17
    @4
    cX
    c.ex
    cvv
    csbov1g
    @39
    @44
    @17
    cX
    c.ex
    vk
    @17
    cvv
    csbvarg
    oveq1d
    eqtrd
    oveq12d
    eqtrd
    ax-mp
    @26
    @36
    @38
    @25
    @37
    c.x
    co
    #
    @15
    @24
    @25
    @37
    c.x
    oveq1
    @36
    @45
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    @37
    c.x
    co
    #
    @15
    @36
    @25
    @47
    @37
    c.x
    @36
    cR
    @46
    c0g
    @3
    cR
    @46
    wceq
    #
    @33
    @35
    @0
    @1
    @49
    @2
    cP
    cR
    crg
    ply1mulgsum.p
    ply1sca
    3ad2ant1
    ad2antrr
    fveq2d
    oveq1d
    @36
    cP
    clmod
    wcel
    #
    @37
    cB
    wcel
    #
    @48
    @15
    wceq
    @3
    @50
    @33
    @35
    @0
    @1
    @50
    @2
    cP
    cR
    ply1mulgsum.p
    ply1lmod
    3ad2ant1
    ad2antrr
    @36
    cM
    cmnd
    wcel
    #
    @35
    cX
    cB
    wcel
    #
    @51
    @3
    @52
    @33
    @35
    @0
    @1
    @52
    @2
    @0
    cP
    crg
    wcel
    @52
    cP
    cR
    ply1mulgsum.p
    ply1ring
    cP
    cM
    ply1mulgsum.m
    ringmgp
    syl
    3ad2ant1
    ad2antrr
    @34
    @35
    simpr
    @3
    @53
    @33
    @35
    @0
    @1
    @53
    @2
    cB
    cP
    cR
    cX
    ply1mulgsum.x
    ply1mulgsum.p
    ply1mulgsum.b
    vr1cl
    3ad2ant1
    ad2antrr
    cB
    c.ex
    cM
    @17
    cX
    cB
    cP
    cM
    ply1mulgsum.m
    ply1mulgsum.b
    mgpbas
    ply1mulgsum.e
    mulgnn0cl
    syl3anc
    c.x
    @46
    @47
    cB
    cP
    @37
    @15
    ply1mulgsum.b
    @46
    eqid
    ply1mulgsum.sm
    @47
    eqid
    @15
    eqid
    lmod0vs
    syl2anc
    eqtrd
    sylan9eqr
    syl5eq
    ex
    imim2d
    ralimdva
    reximdva
    mpd
    mptnn0fsupp
end
