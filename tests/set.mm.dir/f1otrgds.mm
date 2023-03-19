include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimivva.mm"
include "wcel.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem f1otrgds
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
  assert |- ( ph -> ( X E Y ) = ( ( F ` X ) D ( F ` Y ) ) )

  proof
    wph
    ve
    cv
    #
    vf
    cv
    #
    cE
    co
    #
    @0
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cD
    co
    #
    wceq
    #
    vf
    cB
    wral
    ve
    cB
    wral
    #
    cX
    cY
    cE
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cD
    co
    #
    wceq
    #
    wph
    @6
    ve
    vf
    cB
    cB
    f1otrkg.1
    ralrimivva
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @7
    @12
    wi
    f1otrgitv.x
    f1otrgitv.y
    @6
    @12
    cX
    @1
    cE
    co
    #
    @9
    @4
    cD
    co
    #
    wceq
    ve
    vf
    cX
    cY
    cB
    cB
    @0
    cX
    wceq
    #
    @2
    @13
    @5
    @14
    @0
    cX
    @1
    cE
    oveq1
    @15
    @3
    @9
    @4
    cD
    @0
    cX
    cF
    fveq2
    oveq1d
    eqeq12d
    @1
    cY
    wceq
    #
    @13
    @8
    @14
    @11
    @1
    cY
    cX
    cE
    oveq2
    @16
    @4
    @10
    @9
    cD
    @1
    cY
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl2anc
    mpd
end
