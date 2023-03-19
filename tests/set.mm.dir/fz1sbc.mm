include "cz.mm"
include "wcel.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "sbc6g.mm"
include "df-ral.mm"
include "elfz1eq.mm"
include "elfz3.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "impbid2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "syl5rbb.mm"
include "bitr2d.mm"

theorem fz1sbc
  let wph: wff ph
  let vk: setvar k
  let cN: class N

  disjoint N k
  assert |- ( N e. ZZ -> ( A. k e. ( N ... N ) ph <-> [. N / k ]. ph ) )

  proof
    cN
    cz
    wcel
    #
    wph
    vk
    cN
    wsbc
    vk
    cv
    #
    cN
    wceq
    #
    wph
    wi
    #
    vk
    wal
    #
    wph
    vk
    cN
    cN
    cfz
    co
    #
    wral
    #
    wph
    vk
    cN
    cz
    sbc6g
    @6
    @1
    @5
    wcel
    #
    wph
    wi
    #
    vk
    wal
    @0
    @4
    wph
    vk
    @5
    df-ral
    @0
    @8
    @3
    vk
    @0
    @7
    @2
    wph
    @0
    @7
    @2
    @1
    cN
    elfz1eq
    @0
    @7
    @2
    cN
    @5
    wcel
    cN
    elfz3
    @1
    cN
    @5
    eleq1
    syl5ibrcom
    impbid2
    imbi1d
    albidv
    syl5rbb
    bitr2d
end
