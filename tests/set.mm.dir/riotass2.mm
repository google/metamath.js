include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "crio.mm"
include "wsbc.mm"
include "wceq.mm"
include "reuss2.mm"
include "simplr.mm"
include "riotasbc.mm"
include "wcel.mm"
include "riotacl.mm"
include "rspsbc.mm"
include "sbcimg.mm"
include "sylibd.mm"
include "syl.mm"
include "mpid.mm"
include "sylc.mm"
include "wb.mm"
include "ssel.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "simprr.mm"
include "nfriota1.mm"
include "nfsbc1.mm"
include "sbceq1a.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem riotass2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ps ) )

  proof
    cA
    cB
    wss
    #
    wph
    wps
    wi
    #
    vx
    cA
    wral
    #
    wa
    #
    wph
    vx
    cA
    wrex
    #
    wps
    vx
    cB
    wreu
    #
    wa
    #
    wa
    #
    wps
    vx
    cB
    crio
    #
    wph
    vx
    cA
    crio
    #
    @7
    wps
    vx
    @9
    wsbc
    #
    @8
    @9
    wceq
    #
    @7
    wph
    vx
    cA
    wreu
    #
    @2
    @10
    wph
    wps
    vx
    cA
    cB
    reuss2
    #
    @0
    @2
    @6
    simplr
    @12
    @2
    wph
    vx
    @9
    wsbc
    #
    @10
    wph
    vx
    cA
    riotasbc
    @12
    @9
    cA
    wcel
    #
    @2
    @14
    @10
    wi
    #
    wi
    wph
    vx
    cA
    riotacl
    #
    @15
    @2
    @1
    vx
    @9
    wsbc
    @16
    @1
    vx
    @9
    cA
    rspsbc
    wph
    wps
    vx
    @9
    cA
    sbcimg
    sylibd
    syl
    mpid
    sylc
    @7
    @9
    cB
    wcel
    #
    @5
    @10
    @11
    wb
    @7
    @15
    @18
    @7
    @12
    @15
    @13
    @17
    syl
    @0
    @15
    @18
    wi
    @2
    @6
    cA
    cB
    @9
    ssel
    ad2antrr
    mpd
    @3
    @4
    @5
    simprr
    wps
    @10
    vx
    cB
    @9
    wph
    vx
    cA
    nfriota1
    #
    wps
    vx
    @9
    @19
    nfsbc1
    wps
    vx
    @9
    sbceq1a
    riota2f
    syl2anc
    mpbid
    eqcomd
end
