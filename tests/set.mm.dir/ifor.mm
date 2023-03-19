include "wo.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "orcs.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "biorf.mm"
include "ifbid.mm"
include "eqtr2d.mm"
include "pm2.61i.mm"

theorem ifor
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B


  assert |- if ( ( ph \/ ps ) , A , B ) = if ( ph , A , if ( ps , A , B ) )

  proof
    wph
    wph
    wps
    wo
    #
    cA
    cB
    cif
    #
    wph
    cA
    wps
    cA
    cB
    cif
    #
    cif
    #
    wceq
    wph
    @1
    cA
    @3
    wph
    wps
    @1
    cA
    wceq
    @0
    cA
    cB
    iftrue
    orcs
    wph
    cA
    @2
    iftrue
    eqtr4d
    wph
    wn
    #
    @3
    @2
    @1
    wph
    cA
    @2
    iffalse
    @4
    wps
    @0
    cA
    cB
    wph
    wps
    biorf
    ifbid
    eqtr2d
    pm2.61i
end
