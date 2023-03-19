include "wn.mm"
include "wne.mm"
include "notnotb.mm"
include "syl5rbbr.mm"
include "necon4abid.mm"

theorem necon2bbid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon2bbid.1: |- ( ph -> ( ps <-> A =/= B ) )


  assert |- ( ph -> ( A = B <-> -. ps ) )

  proof
    wph
    wps
    wn
    #
    cA
    cB
    @0
    wn
    wps
    wph
    cA
    cB
    wne
    wps
    notnotb
    necon2bbid.1
    syl5rbbr
    necon4abid
end
