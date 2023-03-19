include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "wrex.mm"
include "ctp.mm"
include "wf1.mm"
include "wf.mm"
include "wi.mm"
include "f1f.mm"
include "wa.mm"
include "simpr.mm"
include "wceq.mm"
include "w3o.mm"
include "eqidd.mm"
include "3mix1d.mm"
include "wb.mm"
include "simp1d.mm"
include "eltpg.mm"
include "syl.mm"
include "mpbird.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "3mix2d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "tpid3g.mm"
include "3jca.mm"
include "expcom.mm"
include "mpcom.mm"
include "f1dom3fv3dif.mm"
include "neeq1.mm"
include "3anbi12d.mm"
include "neeq2.mm"
include "3anbi13d.mm"
include "3anbi23d.mm"
include "rspc3ev.mm"
include "syl2anc.mm"

theorem f1dom3el3dif
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ph -> E. x e. R E. y e. R E. z e. R ( x =/= y /\ x =/= z /\ y =/= z ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cR
    wcel
    #
    cB
    cF
    cfv
    #
    cR
    wcel
    #
    cC
    cF
    cfv
    #
    cR
    wcel
    #
    w3a
    #
    @0
    @2
    wne
    #
    @0
    @4
    wne
    #
    @2
    @4
    wne
    #
    w3a
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @11
    vz
    cv
    #
    wne
    #
    @12
    @14
    wne
    #
    w3a
    #
    vz
    cR
    wrex
    vy
    cR
    wrex
    vx
    cR
    wrex
    cA
    cB
    cC
    ctp
    #
    cR
    cF
    wf1
    #
    wph
    @6
    f1dom3fv3dif.f
    @19
    @18
    cR
    cF
    wf
    #
    wph
    @6
    wi
    @18
    cR
    cF
    f1f
    wph
    @20
    @6
    wph
    @20
    wa
    #
    @1
    @3
    @5
    @21
    @18
    cR
    cA
    cF
    wph
    @20
    simpr
    #
    wph
    cA
    @18
    wcel
    #
    @20
    wph
    @23
    cA
    cA
    wceq
    #
    cA
    cB
    wceq
    #
    cA
    cC
    wceq
    #
    w3o
    #
    wph
    @24
    @25
    @26
    wph
    cA
    eqidd
    3mix1d
    wph
    cA
    cX
    wcel
    #
    @23
    @27
    wb
    wph
    @28
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
    adantr
    ffvelrnd
    @21
    @18
    cR
    cB
    cF
    @22
    wph
    cB
    @18
    wcel
    #
    @20
    wph
    @31
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
    @33
    @32
    @34
    wph
    cB
    eqidd
    3mix2d
    wph
    @29
    @31
    @35
    wb
    wph
    @28
    @29
    @30
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
    adantr
    ffvelrnd
    @21
    @18
    cR
    cC
    cF
    @22
    wph
    cC
    @18
    wcel
    #
    @20
    wph
    @30
    @36
    wph
    @28
    @29
    @30
    f1dom3fv3dif.v
    simp3d
    cC
    cZ
    cA
    cB
    tpid3g
    syl
    adantr
    ffvelrnd
    3jca
    expcom
    syl
    mpcom
    wph
    cA
    cB
    cC
    cR
    cF
    cX
    cY
    cZ
    f1dom3fv3dif.v
    f1dom3fv3dif.n
    f1dom3fv3dif.f
    f1dom3fv3dif
    @17
    @10
    @0
    @12
    wne
    #
    @0
    @14
    wne
    #
    @16
    w3a
    @7
    @38
    @2
    @14
    wne
    #
    w3a
    vx
    vy
    vz
    @0
    @2
    @4
    cR
    cR
    cR
    @11
    @0
    wceq
    @13
    @37
    @15
    @38
    @16
    @11
    @0
    @12
    neeq1
    @11
    @0
    @14
    neeq1
    3anbi12d
    @12
    @2
    wceq
    @37
    @7
    @16
    @39
    @38
    @12
    @2
    @0
    neeq2
    @12
    @2
    @14
    neeq1
    3anbi13d
    @14
    @4
    wceq
    @38
    @8
    @39
    @9
    @7
    @14
    @4
    @0
    neeq2
    @14
    @4
    @2
    neeq2
    3anbi23d
    rspc3ev
    syl2anc
end
