include "wcel.mm"
include "cab.mm"
include "wb.mm"
include "wn.mm"
include "elabgf.mm"
include "ibi.mm"
include "pm2.21.mm"
include "impbid2.mm"
include "ja.mm"

theorem elab3gf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elab3gf.1: |- F/_ x A
  assume elab3gf.2: |- F/ x ps
  assume elab3gf.3: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) )

  proof
    wps
    cA
    cB
    wcel
    cA
    wph
    vx
    cab
    #
    wcel
    #
    wps
    wb
    wps
    wn
    @1
    wps
    @1
    wps
    wph
    wps
    vx
    cA
    @0
    elab3gf.1
    elab3gf.2
    elab3gf.3
    elabgf
    ibi
    wps
    @1
    pm2.21
    impbid2
    wph
    wps
    vx
    cA
    cB
    elab3gf.1
    elab3gf.2
    elab3gf.3
    elabgf
    ja
end
