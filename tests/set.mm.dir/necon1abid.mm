include "wn.mm"
include "wne.mm"
include "notnotb.mm"
include "necon3bbid.mm"
include "syl5rbb.mm"

theorem necon1abid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon1abid.1: |- ( ph -> ( -. ps <-> A = B ) )


  assert |- ( ph -> ( A =/= B <-> ps ) )

  proof
    wps
    wps
    wn
    #
    wn
    wph
    cA
    cB
    wne
    wps
    notnotb
    wph
    @0
    cA
    cB
    necon1abid.1
    necon3bbid
    syl5rbb
end
