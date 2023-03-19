include "wceq.mm"
include "wn.mm"
include "necon2bd.mm"
include "notnotr.mm"
include "syl6.mm"

theorem necon4bd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon4bd.1: |- ( ph -> ( -. ps -> A =/= B ) )


  assert |- ( ph -> ( A = B -> ps ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    wn
    #
    wn
    wps
    wph
    @0
    cA
    cB
    necon4bd.1
    necon2bd
    wps
    notnotr
    syl6
end
