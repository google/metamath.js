include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "tgbtwncom.mm"
include "axtgpasch.mm"
include "simprr.mm"
include "simpr.mm"
include "tgbtwnexch2.mm"
include "ex.mm"
include "anim1d.mm"
include "reximdva.mm"
include "mpd.mm"
include "r19.29a.mm"

theorem tgtrisegint
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vq: setvar q
  let vr: setvar r
  let vx: setvar x
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnintr.1: |- ( ph -> A e. P )
  assume tgbtwnintr.2: |- ( ph -> B e. P )
  assume tgbtwnintr.3: |- ( ph -> C e. P )
  assume tgbtwnintr.4: |- ( ph -> D e. P )
  assume tgtrisegint.e: |- ( ph -> E e. P )
  assume tgtrisegint.p: |- ( ph -> F e. P )
  assume tgtrisegint.1: |- ( ph -> B e. ( A I C ) )
  assume tgtrisegint.2: |- ( ph -> E e. ( D I C ) )
  assume tgtrisegint.3: |- ( ph -> F e. ( A I D ) )

  disjoint .- q
  disjoint A q
  disjoint B q
  disjoint C q
  disjoint D q
  disjoint E q
  disjoint F q
  disjoint I q
  disjoint P q
  disjoint ph q
  disjoint q r
  disjoint .- r
  disjoint A r
  disjoint B r
  disjoint C r
  disjoint D r
  disjoint E r
  disjoint F r
  disjoint I r
  disjoint P r
  disjoint ph r
  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint I x
  disjoint P x
  disjoint ph x
  assert |- ( ph -> E. q e. P ( q e. ( F I C ) /\ q e. ( B I E ) ) )

  proof
    wph
    vr
    cv
    #
    cE
    cA
    cI
    co
    wcel
    #
    @0
    cF
    cC
    cI
    co
    #
    wcel
    #
    wa
    #
    vq
    cv
    #
    @2
    wcel
    #
    @5
    cB
    cE
    cI
    co
    wcel
    #
    wa
    #
    vq
    cP
    wrex
    #
    vr
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @4
    wa
    #
    @5
    @0
    cC
    cI
    co
    wcel
    #
    @7
    wa
    #
    vq
    cP
    wrex
    @9
    @12
    cP
    @0
    cG
    cI
    c.mi
    cB
    cE
    cC
    cA
    vq
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    #
    @10
    @4
    tkgeom.g
    ad2antrr
    #
    wph
    cE
    cP
    wcel
    @10
    @4
    tgtrisegint.e
    ad2antrr
    wph
    cC
    cP
    wcel
    #
    @10
    @4
    tgbtwnintr.3
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    @10
    @4
    tgbtwnintr.1
    ad2antrr
    #
    wph
    @10
    @4
    simplr
    #
    wph
    cB
    cP
    wcel
    @10
    @4
    tgbtwnintr.2
    ad2antrr
    #
    @11
    @1
    @3
    simprl
    @12
    cA
    cB
    cC
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @16
    @19
    @21
    @18
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    @10
    @4
    tgtrisegint.1
    ad2antrr
    tgbtwncom
    axtgpasch
    @12
    @14
    @8
    vq
    cP
    @12
    @5
    cP
    wcel
    #
    wa
    #
    @13
    @6
    @7
    @23
    @13
    @6
    @23
    @13
    wa
    cF
    @0
    @5
    cC
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @12
    @15
    @22
    @13
    @16
    ad2antrr
    @12
    cF
    cP
    wcel
    #
    @22
    @13
    wph
    @24
    @10
    @4
    tgtrisegint.p
    ad2antrr
    ad2antrr
    @12
    @10
    @22
    @13
    @20
    ad2antrr
    @12
    @22
    @13
    simplr
    @12
    @17
    @22
    @13
    @18
    ad2antrr
    @12
    @3
    @22
    @13
    @11
    @1
    @3
    simprr
    ad2antrr
    @23
    @13
    simpr
    tgbtwnexch2
    ex
    anim1d
    reximdva
    mpd
    wph
    cP
    cE
    cG
    cI
    c.mi
    cF
    cC
    cA
    cD
    vr
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.3
    tgbtwnintr.1
    tgbtwnintr.4
    tgtrisegint.e
    tgtrisegint.p
    wph
    cD
    cE
    cC
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.4
    tgtrisegint.e
    tgbtwnintr.3
    tgtrisegint.2
    tgbtwncom
    tgtrisegint.3
    axtgpasch
    r19.29a
end
