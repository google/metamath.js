include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "cn.mm"
include "cen.mm"
include "wbr.mm"
include "wral.mm"
include "ciun.mm"
include "com.mm"
include "ominf.mm"
include "wa.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "iunrab.mm"
include "syl6reqr.mm"
include "eleq1d.mm"
include "wb.mm"
include "nnenom.mm"
include "entr.mm"
include "sylancl.mm"
include "enfi.mm"
include "syl.mm"
include "bitrd.mm"
include "mtbiri.mm"
include "iunfi.mm"
include "sylan.mm"
include "mtand.mm"
include "rexnal.mm"
include "wss.mm"
include "jctir.mm"
include "ssrab2.mm"
include "jctl.mm"
include "ctbnfien.mm"
include "syl2an.mm"
include "ex.mm"
include "reximdv.mm"
include "mpd.mm"

theorem fiphp3d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  assume fiphp3d.a: |- ( ph -> A ~~ NN )
  assume fiphp3d.b: |- ( ph -> B e. Fin )
  assume fiphp3d.c: |- ( ( ph /\ x e. A ) -> D e. B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint D y
  assert |- ( ph -> E. y e. B { x e. A | D = y } ~~ NN )

  proof
    wph
    cD
    vy
    cv
    #
    wceq
    #
    vx
    cA
    crab
    #
    cfn
    wcel
    #
    wn
    #
    vy
    cB
    wrex
    #
    @2
    cn
    cen
    wbr
    #
    vy
    cB
    wrex
    wph
    @3
    vy
    cB
    wral
    #
    wn
    @5
    wph
    @7
    vy
    cB
    @2
    ciun
    #
    cfn
    wcel
    #
    wph
    @9
    com
    cfn
    wcel
    #
    ominf
    wph
    @9
    cA
    cfn
    wcel
    #
    @10
    wph
    @8
    cA
    cfn
    wph
    cA
    @1
    vy
    cB
    wrex
    #
    vx
    cA
    crab
    #
    @8
    wph
    @12
    vx
    cA
    wral
    cA
    @13
    wceq
    wph
    @12
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    cD
    cB
    wcel
    #
    @12
    fiphp3d.c
    @14
    @0
    cD
    wceq
    #
    vy
    cB
    wrex
    @12
    vy
    cD
    cB
    risset
    @15
    @1
    vy
    cB
    @0
    cD
    eqcom
    rexbii
    bitri
    sylib
    ralrimiva
    @12
    vx
    cA
    rabid2
    sylibr
    @1
    vy
    vx
    cB
    cA
    iunrab
    syl6reqr
    eleq1d
    wph
    cA
    com
    cen
    wbr
    #
    @11
    @10
    wb
    wph
    cA
    cn
    cen
    wbr
    cn
    com
    cen
    wbr
    #
    @16
    fiphp3d.a
    nnenom
    cA
    cn
    com
    entr
    sylancl
    #
    cA
    com
    enfi
    syl
    bitrd
    mtbiri
    wph
    cB
    cfn
    wcel
    @7
    @9
    fiphp3d.b
    vy
    cB
    @2
    iunfi
    sylan
    mtand
    @3
    vy
    cB
    rexnal
    sylibr
    wph
    @4
    @6
    vy
    cB
    wph
    @4
    @6
    wph
    @16
    @17
    wa
    @2
    cA
    wss
    #
    @4
    wa
    @6
    @4
    wph
    @16
    @17
    @18
    nnenom
    jctir
    @4
    @19
    @1
    vx
    cA
    ssrab2
    jctl
    @2
    cA
    cn
    ctbnfien
    syl2an
    ex
    reximdv
    mpd
end
