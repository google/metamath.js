include "wn.mm"
include "wceq.mm"
include "notnotb.mm"
include "necon1bbid.mm"
include "syl5rbb.mm"

theorem necon4abid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon4abid.1: |- ( ph -> ( A =/= B <-> -. ps ) )


  assert |- ( ph -> ( A = B <-> ps ) )

  proof
    wps
    wps
    wn
    #
    wn
    wph
    cA
    cB
    wceq
    wps
    notnotb
    wph
    @0
    cA
    cB
    necon4abid.1
    necon1bbid
    syl5rbb
end
