include "wceq.mm"
include "wne.mm"
include "wn.mm"
include "df-ne.mm"
include "syl6ib.mm"
include "con2d.mm"

theorem necon2bd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon2bd.1: |- ( ph -> ( ps -> A =/= B ) )


  assert |- ( ph -> ( A = B -> -. ps ) )

  proof
    wph
    wps
    cA
    cB
    wceq
    #
    wph
    wps
    cA
    cB
    wne
    @0
    wn
    necon2bd.1
    cA
    cB
    df-ne
    syl6ib
    con2d
end
