include "wss.mm"
include "wrex.mm"
include "wreu.mm"
include "w3a.mm"
include "crio.mm"
include "wsbc.mm"
include "wceq.mm"
include "reuss.mm"
include "riotasbc.mm"
include "syl.mm"
include "wcel.mm"
include "wb.mm"
include "simp1.mm"
include "riotacl.mm"
include "sseldd.mm"
include "simp3.mm"
include "nfriota1.mm"
include "nfsbc1.mm"
include "sbceq1a.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem riotass
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) )

  proof
    cA
    cB
    wss
    #
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cB
    wreu
    #
    w3a
    #
    wph
    vx
    cB
    crio
    #
    wph
    vx
    cA
    crio
    #
    @3
    wph
    vx
    @5
    wsbc
    #
    @4
    @5
    wceq
    #
    @3
    wph
    vx
    cA
    wreu
    #
    @6
    wph
    vx
    cA
    cB
    reuss
    #
    wph
    vx
    cA
    riotasbc
    syl
    @3
    @5
    cB
    wcel
    @2
    @6
    @7
    wb
    @3
    cA
    cB
    @5
    @0
    @1
    @2
    simp1
    @3
    @8
    @5
    cA
    wcel
    @9
    wph
    vx
    cA
    riotacl
    syl
    sseldd
    @0
    @1
    @2
    simp3
    wph
    @6
    vx
    cB
    @5
    wph
    vx
    cA
    nfriota1
    #
    wph
    vx
    @5
    @10
    nfsbc1
    wph
    vx
    @5
    sbceq1a
    riota2f
    syl2anc
    mpbid
    eqcomd
end
