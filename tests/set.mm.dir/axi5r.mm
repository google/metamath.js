include "wal.mm"
include "wi.mm"
include "hba1.mm"
include "hbim.mm"
include "sp.mm"
include "imim2i.mm"
include "alrimih.mm"

theorem axi5r
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph -> A. x ps ) -> A. x ( A. x ph -> ps ) )

  proof
    wph
    vx
    wal
    #
    wps
    vx
    wal
    #
    wi
    @0
    wps
    wi
    vx
    @0
    @1
    vx
    wph
    vx
    hba1
    wps
    vx
    hba1
    hbim
    @1
    wps
    @0
    wps
    vx
    sp
    imim2i
    alrimih
end
