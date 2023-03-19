include "wb.mm"
include "wal.mm"
include "wssb.mm"
include "wi.mm"
include "biimp.mm"
include "alimi.mm"
include "bj-ssbim.mm"
include "syl.mm"
include "biimpr.mm"
include "impbid.mm"

theorem bj-ssbbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( A. x ( ph <-> ps ) -> ( [b t /b x ]b ph <-> [b t /b x ]b ps ) )

  proof
    wph
    wps
    wb
    #
    vx
    wal
    #
    wph
    vx
    vt
    wssb
    #
    wps
    vx
    vt
    wssb
    #
    @1
    wph
    wps
    wi
    #
    vx
    wal
    @2
    @3
    wi
    @0
    @4
    vx
    wph
    wps
    biimp
    alimi
    wph
    wps
    vx
    vt
    bj-ssbim
    syl
    @1
    wps
    wph
    wi
    #
    vx
    wal
    @3
    @2
    wi
    @0
    @5
    vx
    wph
    wps
    biimpr
    alimi
    wps
    wph
    vx
    vt
    bj-ssbim
    syl
    impbid
end
