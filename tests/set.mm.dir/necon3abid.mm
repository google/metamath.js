include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "notbid.mm"
include "syl5bb.mm"

theorem necon3abid
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  assume necon3abid.1: |- ( ph -> ( A = B <-> ps ) )


  assert |- ( ph -> ( A =/= B <-> -. ps ) )

  proof
    cA
    cB
    wne
    cA
    cB
    wceq
    #
    wn
    wph
    wps
    wn
    cA
    cB
    df-ne
    wph
    @0
    wps
    necon3abid.1
    notbid
    syl5bb
end
