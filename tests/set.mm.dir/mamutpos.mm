include "cv.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "ctpos.mm"
include "eqid.mm"
include "tposmpt2.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "ccrg.mm"
include "wceq.mm"
include "simpl1.mm"
include "syl.mm"
include "cxp.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "3syl.mm"
include "simpl3.mm"
include "simpr.mm"
include "fovrnd.mm"
include "simpl2.mm"
include "crngcom.mm"
include "syl3anc.mm"
include "ovtpos.mm"
include "oveq12i.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "syl5eq.mm"
include "mamuval.mm"
include "tposeqd.mm"
include "tposmap.mm"
include "3eqtr4d.mm"

theorem mamutpos
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume mamutpos.f: |- F = ( R maMul <. M , N , P >. )
  assume mamutpos.g: |- G = ( R maMul <. P , N , M >. )
  assume mamutpos.b: |- B = ( Base ` R )
  assume mamutpos.r: |- ( ph -> R e. CRing )
  assume mamutpos.m: |- ( ph -> M e. Fin )
  assume mamutpos.n: |- ( ph -> N e. Fin )
  assume mamutpos.p: |- ( ph -> P e. Fin )
  assume mamutpos.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mamutpos.y: |- ( ph -> Y e. ( B ^m ( N X. P ) ) )


  assert |- ( ph -> tpos ( X F Y ) = ( tpos Y G tpos X ) )

  proof
    wph
    vj
    vi
    cM
    cP
    cR
    vk
    cN
    vj
    cv
    #
    vk
    cv
    #
    cX
    co
    #
    @1
    vi
    cv
    #
    cY
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    ctpos
    #
    vi
    vj
    cP
    cM
    cR
    vk
    cN
    @3
    @1
    cY
    ctpos
    #
    co
    #
    @1
    @0
    cX
    ctpos
    #
    co
    #
    @5
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cX
    cY
    cF
    co
    #
    ctpos
    @11
    @13
    cG
    co
    wph
    @10
    vi
    vj
    cP
    cM
    @8
    cmpt2
    @18
    vj
    vi
    cM
    cP
    @8
    @9
    @9
    eqid
    tposmpt2
    wph
    vi
    vj
    cP
    cM
    @8
    @17
    wph
    @3
    cP
    wcel
    #
    @0
    cM
    wcel
    #
    w3a
    #
    @7
    @16
    cR
    cgsu
    @22
    vk
    cN
    @6
    @15
    @22
    @1
    cN
    wcel
    #
    wa
    #
    @6
    @4
    @2
    @5
    co
    #
    @15
    @24
    cR
    ccrg
    wcel
    #
    @2
    cB
    wcel
    @4
    cB
    wcel
    @6
    @25
    wceq
    @24
    wph
    @26
    wph
    @20
    @21
    @23
    simpl1
    #
    mamutpos.r
    syl
    @24
    @0
    @1
    cB
    cM
    cN
    cX
    @24
    wph
    cX
    cB
    cM
    cN
    cxp
    #
    cmap
    co
    wcel
    #
    @28
    cB
    cX
    wf
    @27
    mamutpos.x
    cX
    cB
    @28
    elmapi
    3syl
    wph
    @20
    @21
    @23
    simpl3
    @22
    @23
    simpr
    #
    fovrnd
    @24
    @1
    @3
    cB
    cN
    cP
    cY
    @24
    wph
    cY
    cB
    cN
    cP
    cxp
    #
    cmap
    co
    wcel
    #
    @31
    cB
    cY
    wf
    @27
    mamutpos.y
    cY
    cB
    @31
    elmapi
    3syl
    @30
    wph
    @20
    @21
    @23
    simpl2
    fovrnd
    cB
    cR
    @5
    @2
    @4
    mamutpos.b
    @5
    eqid
    #
    crngcom
    syl3anc
    @12
    @4
    @14
    @2
    @5
    @3
    @1
    cY
    ovtpos
    @1
    @0
    cX
    ovtpos
    oveq12i
    syl6eqr
    mpteq2dva
    oveq2d
    mpt2eq3dva
    syl5eq
    wph
    @19
    @9
    wph
    cB
    cP
    cR
    @5
    vj
    vk
    vi
    cF
    cM
    cN
    ccrg
    cX
    cY
    mamutpos.f
    mamutpos.b
    @33
    mamutpos.r
    mamutpos.m
    mamutpos.n
    mamutpos.p
    mamutpos.x
    mamutpos.y
    mamuval
    tposeqd
    wph
    cB
    cM
    cR
    @5
    vi
    vk
    vj
    cG
    cP
    cN
    ccrg
    @11
    @13
    mamutpos.g
    mamutpos.b
    @33
    mamutpos.r
    mamutpos.p
    mamutpos.n
    mamutpos.m
    wph
    @32
    @11
    cB
    cP
    cN
    cxp
    cmap
    co
    wcel
    mamutpos.y
    cY
    cB
    cN
    cP
    tposmap
    syl
    wph
    @29
    @13
    cB
    cN
    cM
    cxp
    cmap
    co
    wcel
    mamutpos.x
    cX
    cB
    cM
    cN
    tposmap
    syl
    mamuval
    3eqtr4d
end
