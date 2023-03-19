include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "olc.mm"
include "anim12i.mm"
include "dfifp4.mm"
include "sylibr.mm"

theorem anifp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps /\ ch ) -> if- ( ph , ps , ch ) )

  proof
    wps
    wch
    wa
    wph
    wn
    #
    wps
    wo
    #
    wph
    wch
    wo
    #
    wa
    wph
    wps
    wch
    wif
    wps
    @1
    wch
    @2
    wps
    @0
    olc
    wch
    wph
    olc
    anim12i
    wph
    wps
    wch
    dfifp4
    sylibr
end
