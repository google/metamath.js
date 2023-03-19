include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "df-mo.mm"
include "df-eu.mm"
include "imbi2i.mm"
include "wn.mm"
include "alnex.mm"
include "pm2.21.mm"
include "alimi.mm"
include "sylbir.mm"
include "eximi.mm"
include "19.23bi.mm"
include "biimp.mm"
include "ja.mm"
include "nfia1.mm"
include "wa.mm"
include "id.mm"
include "ax12v.mm"
include "com12.mm"
include "embantd.mm"
include "spsd.mm"
include "ancld.mm"
include "albiim.mm"
include "syl6ibr.mm"
include "exlimi.mm"
include "eximdv.mm"
include "impbii.mm"
include "3bitri.mm"

theorem mo2v
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( E* x ph <-> E. y A. x ( ph -> x = y ) )

  proof
    wph
    vx
    wmo
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wi
    @0
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    #
    wi
    #
    wph
    @2
    wi
    #
    vx
    wal
    #
    vy
    wex
    #
    wph
    vx
    df-mo
    @1
    @5
    @0
    wph
    vx
    vy
    df-eu
    imbi2i
    @6
    @9
    @0
    @5
    @9
    @0
    wn
    #
    @9
    vy
    @10
    @8
    vy
    @10
    wph
    wn
    #
    vx
    wal
    @8
    wph
    vx
    alnex
    @11
    @7
    vx
    wph
    @2
    pm2.21
    alimi
    sylbir
    eximi
    19.23bi
    @4
    @8
    vy
    @3
    @7
    vx
    wph
    @2
    biimp
    alimi
    eximi
    ja
    @0
    @9
    @5
    @0
    @8
    @4
    vy
    wph
    @8
    @4
    wi
    vx
    @7
    @3
    vx
    nfia1
    wph
    @8
    @8
    @2
    wph
    wi
    vx
    wal
    #
    wa
    @4
    wph
    @8
    @12
    wph
    @7
    @12
    vx
    wph
    wph
    @2
    @12
    wph
    id
    @2
    wph
    @12
    wph
    vx
    vy
    ax12v
    com12
    embantd
    spsd
    ancld
    wph
    @2
    vx
    albiim
    syl6ibr
    exlimi
    eximdv
    com12
    impbii
    3bitri
end
