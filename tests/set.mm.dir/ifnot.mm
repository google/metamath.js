include "wn.mm"
include "cif.mm"
include "wceq.mm"
include "notnot.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem ifnot
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- if ( -. ph , A , B ) = if ( ph , B , A )

  proof
    wph
    wph
    wn
    #
    cA
    cB
    cif
    #
    wph
    cB
    cA
    cif
    #
    wceq
    wph
    @1
    cB
    @2
    wph
    @0
    cA
    cB
    wph
    notnot
    iffalsed
    wph
    cB
    cA
    iftrue
    eqtr4d
    @0
    @1
    cA
    @2
    @0
    cA
    cB
    iftrue
    wph
    cB
    cA
    iffalse
    eqtr4d
    pm2.61i
end
