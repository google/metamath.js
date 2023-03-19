include "ccmp.mm"
include "wcel.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cufil.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "cufl.mm"
include "adantr.mm"
include "cuni.mm"
include "cfi.mm"
include "ctg.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "adantlr.mm"
include "simprl.mm"
include "simprr.mm"
include "alexsublem.mm"
include "pm2.21i.mm"
include "expr.mm"
include "pm2.01d.mm"
include "neqned.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "wb.mm"
include "ctb.mm"
include "fibas.mm"
include "tgtopon.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "fiuni.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "ufilcmp.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem alexsub
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cJ: class J
  let cX: class X
  let vz: setvar z
  let vf: setvar f
  let cF: class F
  assume alexsub.1: |- ( ph -> X e. UFL )
  assume alexsub.2: |- ( ph -> X = U. B )
  assume alexsub.3: |- ( ph -> J = ( topGen ` ( fi ` B ) ) )
  assume alexsub.4: |- ( ( ph /\ ( x C_ B /\ X = U. x ) ) -> E. y e. ( ~P x i^i Fin ) X = U. y )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint J z
  disjoint f ph
  disjoint ph z
  disjoint X f
  disjoint X z
  disjoint F x
  disjoint F y
  disjoint F z
  assert |- ( ph -> J e. Comp )

  proof
    wph
    cJ
    ccmp
    wcel
    #
    cJ
    vf
    cv
    #
    cflim
    co
    #
    c0
    wne
    #
    vf
    cX
    cufil
    cfv
    #
    wral
    #
    wph
    @3
    vf
    @4
    wph
    @1
    @4
    wcel
    #
    wa
    #
    @2
    c0
    @7
    @2
    c0
    wceq
    #
    wph
    @6
    @8
    @8
    wn
    #
    wph
    @6
    @8
    wa
    #
    wa
    #
    @9
    @11
    vx
    vy
    cB
    @1
    cJ
    cX
    wph
    cX
    cufl
    wcel
    #
    @10
    alexsub.1
    adantr
    wph
    cX
    cB
    cuni
    #
    wceq
    @10
    alexsub.2
    adantr
    wph
    cJ
    cB
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    @10
    alexsub.3
    adantr
    wph
    vx
    cv
    #
    cB
    wss
    cX
    @16
    cuni
    wceq
    wa
    cX
    vy
    cv
    cuni
    wceq
    vy
    @16
    cpw
    cfn
    cin
    wrex
    @10
    alexsub.4
    adantlr
    wph
    @6
    @8
    simprl
    wph
    @6
    @8
    simprr
    alexsublem
    pm2.21i
    expr
    pm2.01d
    neqned
    ralrimiva
    wph
    @12
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    @0
    @5
    wb
    alexsub.1
    wph
    cJ
    @14
    cuni
    #
    ctopon
    cfv
    #
    @17
    wph
    cJ
    @15
    @19
    alexsub.3
    @14
    ctb
    wcel
    @15
    @19
    wcel
    cB
    fibas
    @14
    tgtopon
    ax-mp
    syl6eqel
    wph
    cX
    @18
    ctopon
    wph
    cX
    @13
    @18
    alexsub.2
    wph
    cB
    cvv
    wcel
    #
    @13
    @18
    wceq
    wph
    @13
    cvv
    wcel
    @20
    wph
    cX
    @13
    cvv
    alexsub.2
    wph
    @12
    cX
    cvv
    wcel
    alexsub.1
    cX
    cufl
    elex
    syl
    eqeltrrd
    cB
    uniexb
    sylibr
    cB
    cvv
    fiuni
    syl
    eqtrd
    fveq2d
    eleqtrrd
    vf
    cJ
    cX
    ufilcmp
    syl2anc
    mpbird
end
