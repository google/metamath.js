include "wne.mm"
include "wn.mm"
include "necon3abid.mm"
include "notnotb.mm"
include "syl6rbbr.mm"

theorem necon2abid
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume necon2abid.1: |- ( ph -> ( A = B <-> -. ps ) )


  assert |- ( ph -> ( ps <-> A =/= B ) )

  proof
    wph
    cA
    cB
    wne
    wps
    wn
    #
    wn
    wps
    wph
    @0
    cA
    cB
    necon2abid.1
    necon3abid
    wps
    notnotb
    syl6rbbr
end
