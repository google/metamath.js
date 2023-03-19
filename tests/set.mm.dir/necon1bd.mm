include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "syl5bir.mm"
include "con1d.mm"

theorem necon1bd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon1bd.1: |- ( ph -> ( A =/= B -> ps ) )


  assert |- ( ph -> ( -. ps -> A = B ) )

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
    necon1bd.1
    syl5bir
    con1d
end
