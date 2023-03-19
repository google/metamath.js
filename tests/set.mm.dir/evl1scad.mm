include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccrg.mm"
include "crg.mm"
include "wf.mm"
include "crngring.mm"
include "ply1sclf.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "csn.mm"
include "cxp.mm"
include "evl1sca.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "fvconst2g.mm"
include "eqtrd.mm"
include "jca.mm"

theorem evl1scad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cU: class U
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume evl1sca.o: |- O = ( eval1 ` R )
  assume evl1sca.p: |- P = ( Poly1 ` R )
  assume evl1sca.b: |- B = ( Base ` R )
  assume evl1sca.a: |- A = ( algSc ` P )
  assume evl1scad.u: |- U = ( Base ` P )
  assume evl1scad.1: |- ( ph -> R e. CRing )
  assume evl1scad.2: |- ( ph -> X e. B )
  assume evl1scad.3: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( A ` X ) e. U /\ ( ( O ` ( A ` X ) ) ` Y ) = X ) )

  proof
    wph
    cX
    cA
    cfv
    #
    cU
    wcel
    cY
    @0
    cO
    cfv
    #
    cfv
    #
    cX
    wceq
    wph
    cB
    cU
    cX
    cA
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    cB
    cU
    cA
    wf
    evl1scad.1
    cR
    crngring
    cA
    cU
    cP
    cR
    cB
    evl1sca.p
    evl1sca.a
    evl1sca.b
    evl1scad.u
    ply1sclf
    3syl
    evl1scad.2
    ffvelrnd
    wph
    @2
    cY
    cB
    cX
    csn
    cxp
    #
    cfv
    #
    cX
    wph
    cY
    @1
    @4
    wph
    @3
    cX
    cB
    wcel
    #
    @1
    @4
    wceq
    evl1scad.1
    evl1scad.2
    cA
    cB
    cP
    cR
    cO
    cX
    evl1sca.o
    evl1sca.p
    evl1sca.b
    evl1sca.a
    evl1sca
    syl2anc
    fveq1d
    wph
    @6
    cY
    cB
    wcel
    @5
    cX
    wceq
    evl1scad.2
    evl1scad.3
    cB
    cX
    cY
    cB
    fvconst2g
    syl2anc
    eqtrd
    jca
end
