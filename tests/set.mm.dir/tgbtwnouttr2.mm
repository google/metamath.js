include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wne.mm"
include "tgbtwnexch3.mm"
include "simprr.mm"
include "eqidd.mm"
include "tgsegconeq.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "axtgsegcon.mm"
include "r19.29a.mm"

theorem tgbtwnouttr2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnintr.1: |- ( ph -> A e. P )
  assume tgbtwnintr.2: |- ( ph -> B e. P )
  assume tgbtwnintr.3: |- ( ph -> C e. P )
  assume tgbtwnintr.4: |- ( ph -> D e. P )
  assume tgbtwnouttr2.1: |- ( ph -> B =/= C )
  assume tgbtwnouttr2.2: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnouttr2.3: |- ( ph -> C e. ( B I D ) )


  assert |- ( ph -> C e. ( A I D ) )

  proof
    wph
    cC
    cA
    vx
    cv
    #
    cI
    co
    #
    wcel
    #
    cC
    @0
    c.mi
    co
    cC
    cD
    c.mi
    co
    #
    wceq
    #
    wa
    #
    cC
    cA
    cD
    cI
    co
    #
    wcel
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    cC
    @1
    @6
    @8
    @2
    @4
    simprl
    #
    @9
    @0
    cD
    cA
    cI
    @9
    cC
    cC
    cD
    cB
    cP
    @0
    cD
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    @7
    @5
    tkgeom.g
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    @7
    @5
    tgbtwnintr.3
    ad2antrr
    #
    @12
    wph
    cD
    cP
    wcel
    @7
    @5
    tgbtwnintr.4
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    @7
    @5
    tgbtwnintr.2
    ad2antrr
    #
    wph
    @7
    @5
    simplr
    #
    @13
    wph
    cB
    cC
    wne
    @7
    @5
    tgbtwnouttr2.1
    ad2antrr
    @9
    cA
    cB
    cC
    @0
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @11
    wph
    cA
    cP
    wcel
    @7
    @5
    tgbtwnintr.1
    ad2antrr
    @14
    @12
    @15
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    @7
    @5
    tgbtwnouttr2.2
    ad2antrr
    @10
    tgbtwnexch3
    wph
    cC
    cB
    cD
    cI
    co
    wcel
    @7
    @5
    tgbtwnouttr2.3
    ad2antrr
    @8
    @2
    @4
    simprr
    @9
    @3
    eqidd
    tgsegconeq
    oveq2d
    eleqtrd
    wph
    vx
    cC
    cD
    cP
    cG
    cI
    c.mi
    cA
    cC
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgbtwnintr.1
    tgbtwnintr.3
    tgbtwnintr.3
    tgbtwnintr.4
    axtgsegcon
    r19.29a
end
