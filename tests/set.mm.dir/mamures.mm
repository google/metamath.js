include "cv.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "ssid.mm"
include "a1i.mm"
include "resmpt2.mm"
include "syl2anc.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "ovres.mm"
include "3ad2antl2.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"
include "eqid.mm"
include "mamuval.mm"
include "reseq1d.mm"
include "cfn.mm"
include "ssfi.mm"
include "cmap.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "xpss1.mm"
include "fssresd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpfi.mm"
include "elmapd.mm"
include "mpbird.mm"
include "3eqtr4d.mm"

theorem mamures
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume mamures.f: |- F = ( R maMul <. M , N , P >. )
  assume mamures.g: |- G = ( R maMul <. I , N , P >. )
  assume mamures.b: |- B = ( Base ` R )
  assume mamures.r: |- ( ph -> R e. V )
  assume mamures.m: |- ( ph -> M e. Fin )
  assume mamures.n: |- ( ph -> N e. Fin )
  assume mamures.p: |- ( ph -> P e. Fin )
  assume mamures.i: |- ( ph -> I C_ M )
  assume mamures.x: |- ( ph -> X e. ( B ^m ( M X. N ) ) )
  assume mamures.y: |- ( ph -> Y e. ( B ^m ( N X. P ) ) )


  assert |- ( ph -> ( ( X F Y ) |` ( I X. P ) ) = ( ( X |` ( I X. N ) ) G Y ) )

  proof
    wph
    vi
    vj
    cM
    cP
    cR
    vk
    cN
    vi
    cv
    #
    vk
    cv
    #
    cX
    co
    #
    @1
    vj
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
    cI
    cP
    cxp
    #
    cres
    #
    vi
    vj
    cI
    cP
    cR
    vk
    cN
    @0
    @1
    cX
    cI
    cN
    cxp
    #
    cres
    #
    co
    #
    @4
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
    @10
    cres
    @13
    cY
    cG
    co
    wph
    @11
    vi
    vj
    cI
    cP
    @8
    cmpt2
    #
    @18
    wph
    cI
    cM
    wss
    #
    cP
    cP
    wss
    #
    @11
    @20
    wceq
    mamures.i
    @22
    wph
    cP
    ssid
    a1i
    vi
    vj
    cM
    cP
    cI
    cP
    @8
    resmpt2
    syl2anc
    wph
    vi
    vj
    cI
    cP
    @8
    @17
    wph
    @0
    cI
    wcel
    #
    @3
    cP
    wcel
    #
    w3a
    #
    @7
    @16
    cR
    cgsu
    @25
    vk
    cN
    @6
    @15
    @25
    @1
    cN
    wcel
    #
    wa
    #
    @2
    @14
    @4
    @5
    @27
    @14
    @2
    @23
    wph
    @26
    @14
    @2
    wceq
    @24
    @0
    @1
    cI
    cN
    cX
    ovres
    3ad2antl2
    eqcomd
    oveq1d
    mpteq2dva
    oveq2d
    mpt2eq3dva
    eqtrd
    wph
    @19
    @9
    @10
    wph
    cB
    cP
    cR
    @5
    vi
    vk
    vj
    cF
    cM
    cN
    cV
    cX
    cY
    mamures.f
    mamures.b
    @5
    eqid
    #
    mamures.r
    mamures.m
    mamures.n
    mamures.p
    mamures.x
    mamures.y
    mamuval
    reseq1d
    wph
    cB
    cP
    cR
    @5
    vi
    vk
    vj
    cG
    cI
    cN
    cV
    @13
    cY
    mamures.g
    mamures.b
    @28
    mamures.r
    wph
    cM
    cfn
    wcel
    @21
    cI
    cfn
    wcel
    #
    mamures.m
    mamures.i
    cM
    cI
    ssfi
    syl2anc
    #
    mamures.n
    mamures.p
    wph
    @13
    cB
    @12
    cmap
    co
    wcel
    @12
    cB
    @13
    wf
    wph
    cM
    cN
    cxp
    #
    cB
    @12
    cX
    wph
    cX
    cB
    @31
    cmap
    co
    wcel
    @31
    cB
    cX
    wf
    mamures.x
    cX
    cB
    @31
    elmapi
    syl
    wph
    @21
    @12
    @31
    wss
    mamures.i
    cI
    cM
    cN
    xpss1
    syl
    fssresd
    wph
    cB
    @12
    @13
    cvv
    cfn
    cB
    cvv
    wcel
    wph
    cB
    cR
    cbs
    cfv
    cvv
    mamures.b
    cR
    cbs
    fvex
    eqeltri
    a1i
    wph
    @29
    cN
    cfn
    wcel
    @12
    cfn
    wcel
    @30
    mamures.n
    cI
    cN
    xpfi
    syl2anc
    elmapd
    mpbird
    mamures.y
    mamuval
    3eqtr4d
end
