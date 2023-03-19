include "wi.mm"
include "wn.mm"
include "wif.mm"
include "ex.mm"
include "dfifp2.mm"
include "sylanbrc.mm"

theorem ifpimpda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ifpimpda.1: |- ( ( ph /\ ps ) -> ch )
  assume ifpimpda.2: |- ( ( ph /\ -. ps ) -> th )


  assert |- ( ph -> if- ( ps , ch , th ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wn
    #
    wth
    wi
    wps
    wch
    wth
    wif
    wph
    wps
    wch
    ifpimpda.1
    ex
    wph
    @0
    wth
    ifpimpda.2
    ex
    wps
    wch
    wth
    dfifp2
    sylanbrc
end
