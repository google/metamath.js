include "wa.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "ibar.mm"
include "ifbid.mm"
include "eqtr2d.mm"
include "wn.mm"
include "simpl.mm"
include "con3i.mm"
include "iffalsed.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem ifan
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B


  assert |- if ( ( ph /\ ps ) , A , B ) = if ( ph , if ( ps , A , B ) , B )

  proof
    wph
    wph
    wps
    wa
    #
    cA
    cB
    cif
    #
    wph
    wps
    cA
    cB
    cif
    #
    cB
    cif
    #
    wceq
    wph
    @3
    @2
    @1
    wph
    @2
    cB
    iftrue
    wph
    wps
    @0
    cA
    cB
    wph
    wps
    ibar
    ifbid
    eqtr2d
    wph
    wn
    #
    @1
    cB
    @3
    @4
    @0
    cA
    cB
    @0
    wph
    wph
    wps
    simpl
    con3i
    iffalsed
    wph
    @2
    cB
    iffalse
    eqtr4d
    pm2.61i
end
