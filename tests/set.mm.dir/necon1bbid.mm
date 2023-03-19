include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "syl5bbr.mm"
include "con1bid.mm"

theorem necon1bbid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon1bbid.1: |- ( ph -> ( A =/= B <-> ps ) )


  assert |- ( ph -> ( -. ps <-> A = B ) )

  proof
    wph
    cA
    cB
    wceq
    #
    wps
    @0
    wn
    cA
    cB
    wne
    wph
    wps
    cA
    cB
    df-ne
    necon1bbid.1
    syl5bbr
    con1bid
end
