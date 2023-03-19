include "cfv.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "brne0.mm"
include "fvprc.mm"
include "necon1ai.mm"
include "syl.mm"
include "cv.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "3jca.mm"
include "adantr.mm"
include "copab.mm"
include "wceq.mm"
include "a1i.mm"
include "rbropap.mm"
include "pm5.21nii.mm"

theorem brfvopabrbr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume brfvopabrbr.1: |- ( A ` Z ) = { <. x , y >. | ( x ( B ` Z ) y /\ ph ) }
  assume brfvopabrbr.2: |- ( ( x = X /\ y = Y ) -> ( ph <-> ps ) )
  assume brfvopabrbr.3: |- Rel ( B ` Z )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint ps x
  disjoint ps y
  assert |- ( X ( A ` Z ) Y <-> ( X ( B ` Z ) Y /\ ps ) )

  proof
    cX
    cY
    cZ
    cA
    cfv
    #
    wbr
    #
    cZ
    cvv
    wcel
    #
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    w3a
    #
    cX
    cY
    cZ
    cB
    cfv
    #
    wbr
    #
    wps
    wa
    @1
    @2
    @3
    @4
    @1
    @0
    c0
    wne
    @2
    cX
    cY
    @0
    brne0
    @2
    @0
    c0
    cZ
    cA
    fvprc
    necon1ai
    syl
    cX
    cY
    @0
    vx
    cv
    vy
    cv
    @6
    wbr
    wph
    wa
    #
    vx
    vy
    @0
    brfvopabrbr.1
    relopabi
    #
    brrelexi
    cX
    cY
    @0
    @9
    brrelex2i
    3jca
    @7
    @5
    wps
    @7
    @2
    @3
    @4
    @7
    @6
    c0
    wne
    @2
    cX
    cY
    @6
    brne0
    @2
    @6
    c0
    cZ
    cB
    fvprc
    necon1ai
    syl
    cX
    cY
    @6
    brfvopabrbr.3
    brrelexi
    cX
    cY
    @6
    brfvopabrbr.3
    brrelex2i
    3jca
    adantr
    @2
    wph
    wps
    cY
    vx
    cX
    @0
    @6
    cvv
    cvv
    vy
    @0
    @8
    vx
    vy
    copab
    wceq
    @2
    brfvopabrbr.1
    a1i
    brfvopabrbr.2
    rbropap
    pm5.21nii
end
