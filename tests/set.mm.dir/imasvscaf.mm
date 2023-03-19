include "cxp.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "imasvscafn.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "co.mm"
include "cmpt2.mm"
include "ciun.mm"
include "imasvsca.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "ralrimivw.mm"
include "anass1rs.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "fssxp.mm"
include "snssd.mm"
include "xpss2.mm"
include "xpss1.mm"
include "3syl.mm"
include "sstrd.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "dff2.mm"
include "sylanbrc.mm"

theorem imasvscaf
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cZ: class Z
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume imasvscaf.u: |- ( ph -> U = ( F "s R ) )
  assume imasvscaf.v: |- ( ph -> V = ( Base ` R ) )
  assume imasvscaf.f: |- ( ph -> F : V -onto-> B )
  assume imasvscaf.r: |- ( ph -> R e. Z )
  assume imasvscaf.g: |- G = ( Scalar ` R )
  assume imasvscaf.k: |- K = ( Base ` G )
  assume imasvscaf.q: |- .x. = ( .s ` R )
  assume imasvscaf.s: |- .xb = ( .s ` U )
  assume imasvscaf.e: |- ( ( ph /\ ( p e. K /\ a e. V /\ q e. V ) ) -> ( ( F ` a ) = ( F ` q ) -> ( F ` ( p .x. a ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasvscaf.c: |- ( ( ph /\ ( p e. K /\ q e. V ) ) -> ( p .x. q ) e. V )

  disjoint a p
  disjoint a q
  disjoint F a
  disjoint p q
  disjoint F p
  disjoint F q
  disjoint K a
  disjoint K p
  disjoint K q
  disjoint a ph
  disjoint p ph
  disjoint ph q
  disjoint B p
  disjoint B q
  disjoint R p
  disjoint R q
  disjoint .x. p
  disjoint .x. q
  disjoint .xb a
  disjoint .xb p
  disjoint .xb q
  disjoint V a
  disjoint V p
  disjoint V q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint ph w
  disjoint ph x
  disjoint U x
  disjoint B x
  disjoint R x
  disjoint .x. w
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint X p
  disjoint X x
  disjoint Y p
  disjoint Y q
  disjoint Y x
  assert |- ( ph -> .xb : ( K X. B ) --> B )

  proof
    wph
    c.xb
    cK
    cB
    cxp
    #
    wfn
    c.xb
    @0
    cB
    cxp
    #
    wss
    @0
    cB
    c.xb
    wf
    wph
    cB
    cR
    c.xb
    c.x
    cU
    cF
    cG
    cK
    cV
    cZ
    vq
    vp
    va
    imasvscaf.u
    imasvscaf.v
    imasvscaf.f
    imasvscaf.r
    imasvscaf.g
    imasvscaf.k
    imasvscaf.q
    imasvscaf.s
    imasvscaf.e
    imasvscafn
    wph
    c.xb
    vq
    cV
    vp
    vx
    cK
    vq
    cv
    #
    cF
    cfv
    #
    csn
    #
    vp
    cv
    #
    @2
    c.x
    co
    #
    cF
    cfv
    #
    cmpt2
    #
    ciun
    #
    @1
    wph
    vx
    cB
    cR
    c.xb
    c.x
    cU
    cF
    cG
    cK
    cV
    cZ
    vq
    vp
    imasvscaf.u
    imasvscaf.v
    imasvscaf.f
    imasvscaf.r
    imasvscaf.g
    imasvscaf.k
    imasvscaf.q
    imasvscaf.s
    imasvsca
    wph
    @8
    @1
    wss
    #
    vq
    cV
    wral
    @9
    @1
    wss
    wph
    @10
    vq
    cV
    wph
    @2
    cV
    wcel
    #
    wa
    #
    @8
    cK
    @4
    cxp
    #
    cB
    cxp
    #
    @1
    @12
    @13
    cB
    @8
    wf
    #
    @8
    @14
    wss
    @12
    @7
    cB
    wcel
    #
    vx
    @4
    wral
    #
    vp
    cK
    wral
    @15
    @12
    @17
    vp
    cK
    wph
    @5
    cK
    wcel
    #
    @11
    @17
    wph
    @18
    @11
    wa
    #
    wa
    @16
    vx
    @4
    wph
    @19
    @6
    cV
    wcel
    @16
    imasvscaf.c
    wph
    cV
    cB
    @6
    cF
    wph
    cV
    cB
    cF
    wfo
    cV
    cB
    cF
    wf
    imasvscaf.f
    cV
    cB
    cF
    fof
    syl
    #
    ffvelrnda
    syldan
    ralrimivw
    anass1rs
    ralrimiva
    vp
    vx
    cK
    @4
    @7
    cB
    @8
    @8
    eqid
    fmpt2
    sylib
    @13
    cB
    @8
    fssxp
    syl
    @12
    @4
    cB
    wss
    @13
    @0
    wss
    @14
    @1
    wss
    @12
    @3
    cB
    wph
    cV
    cB
    @2
    cF
    @20
    ffvelrnda
    snssd
    @4
    cB
    cK
    xpss2
    @13
    @0
    cB
    xpss1
    3syl
    sstrd
    ralrimiva
    vq
    cV
    @8
    @1
    iunss
    sylibr
    eqsstrd
    @0
    cB
    c.xb
    dff2
    sylanbrc
end
