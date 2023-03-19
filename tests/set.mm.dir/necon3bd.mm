include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "nne.mm"
include "syl5bi.mm"
include "con1d.mm"

theorem necon3bd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon3bd.1: |- ( ph -> ( A = B -> ps ) )


  assert |- ( ph -> ( -. ps -> A =/= B ) )

  proof
    wph
    cA
    cB
    wne
    #
    wps
    @0
    wn
    cA
    cB
    wceq
    wph
    wps
    cA
    cB
    nne
    necon3bd.1
    syl5bi
    con1d
end
