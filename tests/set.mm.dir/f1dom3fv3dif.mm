include "cfv.mm"
include "wne.mm"
include "simp1d.mm"
include "ctp.mm"
include "wf1.mm"
include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "w3o.mm"
include "eqidd.mm"
include "3mix1d.mm"
include "eltpg.mm"
include "syl.mm"
include "mpbird.mm"
include "3mix2d.mm"
include "simp2d.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "necon3bid.mm"
include "simp3d.mm"
include "tpid3g.mm"
include "3jca.mm"

theorem f1dom3fv3dif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume f1dom3fv3dif.v: |- ( ph -> ( A e. X /\ B e. Y /\ C e. Z ) )
  assume f1dom3fv3dif.n: |- ( ph -> ( A =/= B /\ A =/= C /\ B =/= C ) )
  assume f1dom3fv3dif.f: |- ( ph -> F : { A , B , C } -1-1-> R )


  assert |- ( ph -> ( ( F ` A ) =/= ( F ` B ) /\ ( F ` A ) =/= ( F ` C ) /\ ( F ` B ) =/= ( F ` C ) ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wne
    #
    @0
    cC
    cF
    cfv
    #
    wne
    #
    @1
    @3
    wne
    #
    wph
    @2
    cA
    cB
    wne
    #
    wph
    @6
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    f1dom3fv3dif.n
    simp1d
    wph
    @0
    @1
    cA
    cB
    wph
    cA
    cB
    cC
    ctp
    #
    cR
    cF
    wf1
    #
    cA
    @9
    wcel
    #
    cB
    @9
    wcel
    #
    @0
    @1
    wceq
    cA
    cB
    wceq
    #
    wb
    f1dom3fv3dif.f
    wph
    @11
    cA
    cA
    wceq
    #
    @13
    cA
    cC
    wceq
    #
    w3o
    #
    wph
    @14
    @13
    @15
    wph
    cA
    eqidd
    3mix1d
    wph
    cA
    cX
    wcel
    #
    @11
    @16
    wb
    wph
    @17
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    f1dom3fv3dif.v
    simp1d
    cA
    cA
    cB
    cC
    cX
    eltpg
    syl
    mpbird
    #
    wph
    @12
    cB
    cA
    wceq
    #
    cB
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    w3o
    #
    wph
    @22
    @21
    @23
    wph
    cB
    eqidd
    3mix2d
    wph
    @18
    @12
    @24
    wb
    wph
    @17
    @18
    @19
    f1dom3fv3dif.v
    simp2d
    cB
    cA
    cB
    cC
    cY
    eltpg
    syl
    mpbird
    #
    @9
    cR
    cA
    cB
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    wph
    @4
    @7
    wph
    @6
    @7
    @8
    f1dom3fv3dif.n
    simp2d
    wph
    @0
    @3
    cA
    cC
    wph
    @10
    @11
    cC
    @9
    wcel
    #
    @0
    @3
    wceq
    @15
    wb
    f1dom3fv3dif.f
    @20
    wph
    @19
    @26
    wph
    @17
    @18
    @19
    f1dom3fv3dif.v
    simp3d
    cC
    cZ
    cA
    cB
    tpid3g
    syl
    #
    @9
    cR
    cA
    cC
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    wph
    @5
    @8
    wph
    @6
    @7
    @8
    f1dom3fv3dif.n
    simp3d
    wph
    @1
    @3
    cB
    cC
    wph
    @10
    @12
    @26
    @1
    @3
    wceq
    @23
    wb
    f1dom3fv3dif.f
    @25
    @27
    @9
    cR
    cB
    cC
    cF
    f1fveq
    syl12anc
    necon3bid
    mpbird
    3jca
end
