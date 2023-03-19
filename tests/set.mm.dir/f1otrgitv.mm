include "cv.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "ralrimivvva.mm"
include "wi.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "bibi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mpd.mm"

theorem f1otrgitv
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume f1otrkg.p: |- P = ( Base ` G )
  assume f1otrkg.d: |- D = ( dist ` G )
  assume f1otrkg.i: |- I = ( Itv ` G )
  assume f1otrkg.b: |- B = ( Base ` H )
  assume f1otrkg.e: |- E = ( dist ` H )
  assume f1otrkg.j: |- J = ( Itv ` H )
  assume f1otrkg.f: |- ( ph -> F : B -1-1-onto-> P )
  assume f1otrkg.1: |- ( ( ph /\ ( e e. B /\ f e. B ) ) -> ( e E f ) = ( ( F ` e ) D ( F ` f ) ) )
  assume f1otrkg.2: |- ( ( ph /\ ( e e. B /\ f e. B /\ g e. B ) ) -> ( g e. ( e J f ) <-> ( F ` g ) e. ( ( F ` e ) I ( F ` f ) ) ) )
  assume f1otrgitv.x: |- ( ph -> X e. B )
  assume f1otrgitv.y: |- ( ph -> Y e. B )
  assume f1otrgitv.z: |- ( ph -> Z e. B )

  disjoint e f
  disjoint e g
  disjoint B e
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint D e
  disjoint D f
  disjoint E e
  disjoint E f
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint J e
  disjoint J f
  disjoint J g
  disjoint X e
  disjoint X f
  disjoint X g
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint Y f
  disjoint Y g
  disjoint Z g
  assert |- ( ph -> ( Z e. ( X J Y ) <-> ( F ` Z ) e. ( ( F ` X ) I ( F ` Y ) ) ) )

  proof
    wph
    vg
    cv
    #
    ve
    cv
    #
    vf
    cv
    #
    cJ
    co
    #
    wcel
    #
    @0
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    cI
    co
    #
    wcel
    #
    wb
    #
    vg
    cB
    wral
    vf
    cB
    wral
    ve
    cB
    wral
    #
    cZ
    cX
    cY
    cJ
    co
    #
    wcel
    #
    cZ
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cI
    co
    #
    wcel
    #
    wb
    #
    wph
    @10
    ve
    vf
    vg
    cB
    cB
    cB
    f1otrkg.2
    ralrimivvva
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    @11
    @19
    wi
    f1otrgitv.x
    f1otrgitv.y
    f1otrgitv.z
    @10
    @19
    @0
    cX
    @2
    cJ
    co
    #
    wcel
    #
    @5
    @15
    @7
    cI
    co
    #
    wcel
    #
    wb
    @0
    @12
    wcel
    #
    @5
    @17
    wcel
    #
    wb
    ve
    vf
    vg
    cX
    cY
    cZ
    cB
    cB
    cB
    @1
    cX
    wceq
    #
    @4
    @21
    @9
    @23
    @26
    @3
    @20
    @0
    @1
    cX
    @2
    cJ
    oveq1
    eleq2d
    @26
    @8
    @22
    @5
    @26
    @6
    @15
    @7
    cI
    @1
    cX
    cF
    fveq2
    oveq1d
    eleq2d
    bibi12d
    @2
    cY
    wceq
    #
    @21
    @24
    @23
    @25
    @27
    @20
    @12
    @0
    @2
    cY
    cX
    cJ
    oveq2
    eleq2d
    @27
    @22
    @17
    @5
    @27
    @7
    @16
    @15
    cI
    @2
    cY
    cF
    fveq2
    oveq2d
    eleq2d
    bibi12d
    @0
    cZ
    wceq
    #
    @24
    @13
    @25
    @18
    @0
    cZ
    @12
    eleq1
    @28
    @5
    @14
    @17
    @0
    cZ
    cF
    fveq2
    eleq1d
    bibi12d
    rspc3v
    syl3anc
    mpd
end
