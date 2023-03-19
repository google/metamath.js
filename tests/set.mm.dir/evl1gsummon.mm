include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cfv.mm"
include "cpws.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "cbs.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ply1lmod.mm"
include "adantr.mm"
include "r19.21bi.mm"
include "wceq.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "cmnd.mm"
include "cn0.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "lmodvscl.mm"
include "evl1gsumaddval.mm"
include "evl1scvarpwval.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem evl1gsummon
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume evl1gsummon.q: |- Q = ( eval1 ` R )
  assume evl1gsummon.k: |- K = ( Base ` R )
  assume evl1gsummon.w: |- W = ( Poly1 ` R )
  assume evl1gsummon.b: |- B = ( Base ` W )
  assume evl1gsummon.x: |- X = ( var1 ` R )
  assume evl1gsummon.h: |- H = ( mulGrp ` R )
  assume evl1gsummon.e: |- E = ( .g ` H )
  assume evl1gsummon.g: |- G = ( mulGrp ` W )
  assume evl1gsummon.p: |- .^ = ( .g ` G )
  assume evl1gsummon.t1: |- .X. = ( .s ` W )
  assume evl1gsummon.t2: |- .x. = ( .r ` R )
  assume evl1gsummon.r: |- ( ph -> R e. CRing )
  assume evl1gsummon.a: |- ( ph -> A. x e. M A e. K )
  assume evl1gsummon.m: |- ( ph -> M C_ NN0 )
  assume evl1gsummon.f: |- ( ph -> M e. Fin )
  assume evl1gsummon.n: |- ( ph -> A. x e. M N e. NN0 )
  assume evl1gsummon.c: |- ( ph -> C e. K )

  disjoint B x
  disjoint C x
  disjoint K x
  disjoint M x
  disjoint Q x
  disjoint R x
  disjoint ph x
  assert |- ( ph -> ( ( Q ` ( W gsum ( x e. M |-> ( A .X. ( N .^ X ) ) ) ) ) ` C ) = ( R gsum ( x e. M |-> ( A .x. ( N E C ) ) ) ) )

  proof
    wph
    cC
    cW
    vx
    cM
    cA
    cN
    cX
    c.ex
    co
    #
    c.xp
    co
    #
    cmpt
    cgsu
    co
    cQ
    cfv
    cfv
    cR
    vx
    cM
    cC
    @1
    cQ
    cfv
    cfv
    #
    cmpt
    #
    cgsu
    co
    cR
    vx
    cM
    cA
    cN
    cC
    cE
    co
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    vx
    cB
    cC
    cR
    cK
    cpws
    co
    #
    cQ
    cR
    cK
    cM
    cW
    @1
    evl1gsummon.q
    evl1gsummon.k
    evl1gsummon.w
    @6
    eqid
    evl1gsummon.b
    evl1gsummon.r
    wph
    vx
    cv
    cM
    wcel
    #
    wa
    #
    cW
    clmod
    wcel
    #
    cA
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    wph
    @9
    @7
    wph
    cR
    crg
    wcel
    #
    @9
    wph
    cR
    ccrg
    wcel
    #
    @13
    evl1gsummon.r
    cR
    crngring
    syl
    #
    cW
    cR
    evl1gsummon.w
    ply1lmod
    syl
    adantr
    @8
    cA
    cK
    @11
    wph
    cA
    cK
    wcel
    vx
    cM
    evl1gsummon.a
    r19.21bi
    #
    wph
    cK
    @11
    wceq
    @7
    wph
    cK
    cR
    cbs
    cfv
    @11
    evl1gsummon.k
    wph
    cR
    @10
    cbs
    wph
    @14
    cR
    @10
    wceq
    evl1gsummon.r
    cW
    cR
    ccrg
    evl1gsummon.w
    ply1sca
    syl
    fveq2d
    syl5eq
    adantr
    eleqtrd
    @8
    cG
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    @12
    wph
    @17
    @7
    wph
    cW
    crg
    wcel
    #
    @17
    wph
    @13
    @20
    @15
    cW
    cR
    evl1gsummon.w
    ply1ring
    syl
    cW
    cG
    evl1gsummon.g
    ringmgp
    syl
    adantr
    wph
    @18
    vx
    cM
    evl1gsummon.n
    r19.21bi
    #
    @8
    @13
    @19
    wph
    @13
    @7
    @15
    adantr
    cB
    cW
    cR
    cX
    evl1gsummon.x
    evl1gsummon.w
    evl1gsummon.b
    vr1cl
    syl
    cB
    c.ex
    cG
    cN
    cX
    cB
    cW
    cG
    evl1gsummon.g
    evl1gsummon.b
    mgpbas
    evl1gsummon.p
    mulgnn0cl
    syl3anc
    cA
    c.xp
    @10
    @11
    cB
    cW
    @0
    evl1gsummon.b
    @10
    eqid
    evl1gsummon.t1
    @11
    eqid
    lmodvscl
    syl3anc
    evl1gsummon.m
    evl1gsummon.f
    evl1gsummon.c
    evl1gsumaddval
    wph
    @3
    @5
    cR
    cgsu
    wph
    vx
    cM
    @2
    @4
    @8
    cA
    cK
    cC
    cQ
    cR
    c.x
    c.xp
    cE
    c.ex
    cG
    cH
    cN
    cW
    cX
    evl1gsummon.q
    evl1gsummon.w
    evl1gsummon.g
    evl1gsummon.x
    evl1gsummon.k
    evl1gsummon.p
    wph
    @14
    @7
    evl1gsummon.r
    adantr
    @21
    evl1gsummon.t1
    @16
    wph
    cC
    cK
    wcel
    @7
    evl1gsummon.c
    adantr
    evl1gsummon.h
    evl1gsummon.e
    evl1gsummon.t2
    evl1scvarpwval
    mpteq2dva
    oveq2d
    eqtrd
end
