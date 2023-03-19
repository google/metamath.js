include "ax-1.mm"
include "wi.mm"
include "a1i.mm"
include "impbid.mm"
include "ax-mp.mm"
include "impbii.mm"
include "sylibr.mm"
include "bitrd.mm"

theorem confun
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume confun.1: |- ph
  assume confun.2: |- ( ch -> ps )
  assume confun.3: |- ( ch -> th )
  assume confun.4: |- ( ph -> ( ph -> ps ) )


  assert |- ( ch -> ( th <-> ph ) )

  proof
    wch
    wth
    wch
    wph
    wch
    wth
    wch
    wch
    wth
    ax-1
    wch
    wth
    wi
    wch
    confun.3
    a1i
    impbid
    wch
    wch
    wph
    wch
    wph
    wi
    wch
    wch
    wps
    wph
    confun.2
    wph
    wps
    wph
    wph
    wps
    wi
    confun.1
    confun.4
    ax-mp
    wph
    wps
    wph
    wi
    confun.1
    wph
    wps
    ax-1
    ax-mp
    impbii
    sylibr
    a1i
    wch
    wph
    ax-1
    impbid
    bitrd
end
