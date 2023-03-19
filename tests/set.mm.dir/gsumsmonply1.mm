include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "nn0ex.mm"
include "a1i.mm"
include "r19.21bi.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simp2.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "mpd3an3.mm"
include "fmptd.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "syl.mm"
include "csca.mm"
include "wceq.mm"
include "ply1sca.mm"
include "ply1moncl.mm"
include "sylan.mm"
include "mptscmfsupp0.mm"
include "gsumcl.mm"

theorem gsumsmonply1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume gsummonply1.p: |- P = ( Poly1 ` R )
  assume gsummonply1.b: |- B = ( Base ` P )
  assume gsummonply1.x: |- X = ( var1 ` R )
  assume gsummonply1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume gsummonply1.r: |- ( ph -> R e. Ring )
  assume gsummonply1.k: |- K = ( Base ` R )
  assume gsummonply1.m: |- .* = ( .s ` P )
  assume gsummonply1.0: |- .0. = ( 0g ` R )
  assume gsummonply1.a: |- ( ph -> A. k e. NN0 A e. K )
  assume gsummonply1.f: |- ( ph -> ( k e. NN0 |-> A ) finSupp .0. )

  disjoint B k
  disjoint K k
  disjoint k ph
  disjoint .* k
  assert |- ( ph -> ( P gsum ( k e. NN0 |-> ( A .* ( k .^ X ) ) ) ) e. B )

  proof
    wph
    cn0
    cB
    vk
    cn0
    cA
    vk
    cv
    #
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cP
    cvv
    cP
    c0g
    cfv
    #
    gsummonply1.b
    @4
    eqid
    #
    wph
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    cP
    ccmn
    wcel
    gsummonply1.r
    cP
    cR
    gsummonply1.p
    ply1ring
    cP
    ringcmn
    3syl
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    #
    wph
    vk
    cn0
    @2
    cB
    @3
    wph
    @0
    cn0
    wcel
    #
    cA
    cK
    wcel
    #
    @2
    cB
    wcel
    #
    wph
    @9
    vk
    cn0
    gsummonply1.a
    r19.21bi
    #
    wph
    @8
    @9
    w3a
    @6
    @9
    @8
    @10
    wph
    @8
    @6
    @9
    gsummonply1.r
    3ad2ant1
    wph
    @8
    @9
    simp3
    wph
    @8
    @9
    simp2
    cB
    cA
    @0
    cP
    cR
    c.as
    c.ex
    cK
    cP
    cmgp
    cfv
    #
    cX
    gsummonply1.k
    gsummonply1.p
    gsummonply1.x
    gsummonply1.m
    @12
    eqid
    #
    gsummonply1.e
    gsummonply1.b
    ply1tmcl
    syl3anc
    mpd3an3
    @3
    eqid
    fmptd
    wph
    cK
    cn0
    cP
    cR
    cA
    vk
    c.as
    cB
    cvv
    @1
    @4
    c.0
    @7
    wph
    @6
    cP
    clmod
    wcel
    gsummonply1.r
    cP
    cR
    gsummonply1.p
    ply1lmod
    syl
    wph
    @6
    cR
    cP
    csca
    cfv
    wceq
    gsummonply1.r
    cP
    cR
    crg
    gsummonply1.p
    ply1sca
    syl
    gsummonply1.b
    @11
    wph
    @6
    @8
    @1
    cB
    wcel
    gsummonply1.r
    cB
    @0
    cP
    cR
    c.ex
    @12
    cX
    gsummonply1.p
    gsummonply1.x
    @13
    gsummonply1.e
    gsummonply1.b
    ply1moncl
    sylan
    @5
    gsummonply1.0
    gsummonply1.m
    gsummonply1.f
    mptscmfsupp0
    gsumcl
end
