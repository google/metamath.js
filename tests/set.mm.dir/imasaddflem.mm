include "cxp.mm"
include "wfn.mm"
include "wss.mm"
include "wf.mm"
include "imasaddfnlem.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "co.mm"
include "csn.mm"
include "ciun.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "opelxpi.mm"
include "sylan.mm"
include "syldan.mm"
include "syl2anc.mm"
include "snssd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "dff2.mm"
include "sylanbrc.mm"

theorem imasaddflem
  let wph: wff ph
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cV: class V
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cR: class R
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let vx: setvar x
  let cY: class Y
  assume imasaddf.f: |- ( ph -> F : V -onto-> B )
  assume imasaddf.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasaddflem.a: |- ( ph -> .xb = U_ p e. V U_ q e. V { <. <. ( F ` p ) , ( F ` q ) >. , ( F ` ( p .x. q ) ) >. } )
  assume imasaddflem.c: |- ( ( ph /\ ( p e. V /\ q e. V ) ) -> ( p .x. q ) e. V )

  disjoint p q
  disjoint B p
  disjoint B q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint V a
  disjoint b p
  disjoint b q
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .x. p
  disjoint .x. q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint .xb a
  disjoint .xb b
  disjoint .xb p
  disjoint .xb q
  disjoint R p
  disjoint R q
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q y
  disjoint q z
  disjoint w y
  disjoint w z
  disjoint V w
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint .x. w
  disjoint X p
  disjoint a x
  disjoint b x
  disjoint p x
  disjoint q x
  disjoint w x
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph w
  disjoint .xb w
  disjoint .xb x
  disjoint .xb y
  disjoint .xb z
  disjoint Y p
  disjoint Y q
  assert |- ( ph -> .xb : ( B X. B ) --> B )

  proof
    wph
    c.xb
    cB
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
    c.xb
    c.x
    cF
    cV
    vq
    vp
    va
    vb
    imasaddf.f
    imasaddf.e
    imasaddflem.a
    imasaddfnlem
    wph
    c.xb
    vp
    cV
    vq
    cV
    vp
    cv
    #
    cF
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @2
    @4
    c.x
    co
    #
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    ciun
    #
    @1
    imasaddflem.a
    wph
    @11
    @1
    wss
    #
    vp
    cV
    wral
    @12
    @1
    wss
    wph
    @13
    vp
    cV
    wph
    @2
    cV
    wcel
    #
    wa
    #
    @10
    @1
    wss
    #
    vq
    cV
    wral
    @13
    @15
    @16
    vq
    cV
    wph
    @14
    @4
    cV
    wcel
    #
    @16
    wph
    @14
    @17
    wa
    #
    wa
    #
    @9
    @1
    @19
    @6
    @0
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    @1
    wcel
    wph
    cV
    cB
    cF
    wf
    #
    @18
    @20
    wph
    cV
    cB
    cF
    wfo
    @22
    imasaddf.f
    cV
    cB
    cF
    fof
    syl
    #
    @22
    @18
    wa
    @3
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    @20
    @22
    @14
    @24
    @17
    @25
    cV
    cB
    @2
    cF
    ffvelrn
    cV
    cB
    @4
    cF
    ffvelrn
    anim12dan
    @3
    @5
    cB
    cB
    opelxpi
    syl
    sylan
    wph
    @18
    @7
    cV
    wcel
    #
    @21
    imasaddflem.c
    wph
    @22
    @26
    @21
    @23
    cV
    cB
    @7
    cF
    ffvelrn
    sylan
    syldan
    @6
    @8
    @0
    cB
    opelxpi
    syl2anc
    snssd
    anassrs
    ralrimiva
    vq
    cV
    @10
    @1
    iunss
    sylibr
    ralrimiva
    vp
    cV
    @11
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
