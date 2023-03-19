include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "crio.mm"
include "ralrimiva.mm"
include "wi.mm"
include "wsbc.mm"
include "wcel.mm"
include "wa.mm"
include "wtru.mm"
include "a1tru.mm"
include "wreu.mm"
include "reu6i.mm"
include "adantl.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfcvd.mm"
include "nfvd.mm"
include "simprl.mm"
include "simpr.mm"
include "simplrr.mm"
include "simplrl.mm"
include "eqeltrd.mm"
include "rsp.mm"
include "sylc.mm"
include "mpbird.mm"
include "2thd.mm"
include "riota2df.mm"
include "mpdan.mm"
include "mpbid.mm"
include "expr.mm"
include "rspsbc.mm"
include "nfeqd.mm"
include "nfan1.mm"
include "eqeq2d.mm"
include "bibi2d.mm"
include "ralbid.mm"
include "imbi12d.mm"
include "sbcied.mm"
include "mpd.mm"

theorem riota5f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume riota5f.1: |- ( ph -> F/_ x B )
  assume riota5f.2: |- ( ph -> B e. A )
  assume riota5f.3: |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  disjoint ps y
  assert |- ( ph -> ( iota_ x e. A ps ) = B )

  proof
    wph
    wps
    vx
    cv
    #
    cB
    wceq
    #
    wb
    #
    vx
    cA
    wral
    #
    wps
    vx
    cA
    crio
    #
    cB
    wceq
    #
    wph
    @2
    vx
    cA
    riota5f.3
    ralrimiva
    wph
    wps
    @0
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    cA
    wral
    #
    @4
    @6
    wceq
    #
    wi
    #
    vy
    cB
    wsbc
    #
    @3
    @5
    wi
    #
    wph
    cB
    cA
    wcel
    @11
    vy
    cA
    wral
    @12
    riota5f.2
    wph
    @11
    vy
    cA
    wph
    @6
    cA
    wcel
    #
    @9
    @10
    wph
    @14
    @9
    wa
    #
    wa
    #
    wtru
    @10
    @16
    a1tru
    @16
    wps
    vx
    cA
    wreu
    #
    wtru
    @10
    wb
    @15
    @17
    wph
    wps
    vx
    cA
    @6
    reu6i
    adantl
    @16
    wps
    wtru
    vx
    cA
    @6
    wph
    @15
    vx
    wph
    vx
    nfv
    #
    @14
    @9
    vx
    @14
    vx
    nfv
    @8
    vx
    cA
    nfra1
    nfan
    nfan
    @16
    vx
    @6
    nfcvd
    @16
    wtru
    vx
    nfvd
    wph
    @14
    @9
    simprl
    @16
    @7
    wa
    #
    wps
    wtru
    @19
    wps
    @7
    @16
    @7
    simpr
    #
    @19
    @9
    @0
    cA
    wcel
    @8
    wph
    @14
    @9
    @7
    simplrr
    @19
    @0
    @6
    cA
    @20
    wph
    @14
    @9
    @7
    simplrl
    eqeltrd
    @8
    vx
    cA
    rsp
    sylc
    mpbird
    @19
    a1tru
    2thd
    riota2df
    mpdan
    mpbid
    expr
    ralrimiva
    @11
    vy
    cB
    cA
    rspsbc
    sylc
    wph
    @11
    @13
    vy
    cB
    cA
    riota5f.2
    wph
    @6
    cB
    wceq
    #
    wa
    #
    @9
    @3
    @10
    @5
    @22
    @8
    @2
    vx
    cA
    wph
    @21
    vx
    @18
    wph
    vx
    @6
    cB
    wph
    vx
    @6
    nfcvd
    riota5f.1
    nfeqd
    nfan1
    @22
    @7
    @1
    wps
    @22
    @6
    cB
    @0
    wph
    @21
    simpr
    #
    eqeq2d
    bibi2d
    ralbid
    @22
    @6
    cB
    @4
    @23
    eqeq2d
    imbi12d
    sbcied
    mpbid
    mpd
end
