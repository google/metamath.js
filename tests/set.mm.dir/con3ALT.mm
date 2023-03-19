include "wi.mm"
include "wn.mm"
include "wif.mm"
include "wb.mm"
include "bicom1.mm"
include "notbid.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "id.mm"
include "elimh.mm"
include "con3i.mm"
include "dedt.mm"

theorem con3ALT
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) )

  proof
    wps
    wph
    wph
    wps
    wi
    #
    wps
    wn
    #
    wph
    wn
    #
    wi
    @0
    wps
    wph
    wif
    #
    wn
    #
    @2
    wi
    @3
    wps
    wb
    #
    @1
    @4
    @2
    @5
    wps
    @3
    @3
    wps
    bicom1
    #
    notbid
    imbi1d
    wph
    @3
    wps
    wph
    @0
    wph
    wph
    wi
    wph
    @3
    wi
    @5
    wps
    @3
    wph
    @6
    imbi2d
    @3
    wph
    wb
    wph
    @3
    wph
    @3
    wph
    bicom1
    imbi2d
    wph
    id
    elimh
    con3i
    dedt
end
