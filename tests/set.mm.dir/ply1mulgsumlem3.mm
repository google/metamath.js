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
include "ax-mp.mm"
include "simpr.mm"
include "syl5eq.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "mptnn0fsupp.mm"

theorem ply1mulgsumlem3
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
  disjoint k x
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> ( k e. NN0 |-> ( R gsum ( l e. ( 0 ... k ) |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) ) finSupp ( 0g ` R ) )

  proof
    cR
    crg
    wcel
    cK
    cB
    wcel
    cL
    cB
    wcel
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
    @1
    @3
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
    vk
    cvv
    cR
    c0g
    cfv
    #
    vs
    @0
    cR
    c0g
    fvexd
    @0
    @1
    cn0
    wcel
    wa
    cR
    @8
    cgsu
    ovexd
    @0
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
    @12
    cfz
    co
    #
    @4
    @12
    @3
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
    @10
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
    @13
    vk
    @12
    @9
    csb
    #
    @10
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
    @0
    @22
    @26
    vs
    cn0
    @0
    @11
    cn0
    wcel
    wa
    #
    @21
    @25
    vn
    cn0
    @27
    @12
    cn0
    wcel
    wa
    #
    @20
    @24
    @13
    @28
    @20
    @24
    @28
    @20
    wa
    @23
    @19
    @10
    @12
    cvv
    wcel
    #
    @23
    @19
    wceq
    vn
    vex
    @29
    @23
    cR
    vk
    @12
    @8
    csb
    #
    cgsu
    co
    @19
    vk
    @12
    cR
    @8
    cgsu
    cvv
    csbov2g
    @29
    @30
    @18
    cR
    cgsu
    @29
    vk
    @12
    @8
    @18
    cvv
    @29
    id
    @1
    @12
    wceq
    #
    @8
    @18
    wceq
    @29
    @31
    vl
    @2
    @7
    @14
    @17
    @1
    @12
    cc0
    cfz
    oveq2
    @31
    @6
    @16
    @4
    c.as
    @31
    @5
    @15
    cC
    @1
    @12
    @3
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    adantl
    csbied
    oveq2d
    eqtrd
    ax-mp
    @28
    @20
    simpr
    syl5eq
    ex
    imim2d
    ralimdva
    reximdva
    mpd
    mptnn0fsupp
end
