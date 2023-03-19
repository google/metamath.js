include "wn.mm"
include "wb.mm"
include "wi.mm"
include "idn1.mm"
include "biimpr.mm"
include "e1a.mm"
include "con3.mm"
include "notnotb.mm"
include "imbi2.mm"
include "biimprcd.mm"
include "e10.mm"
include "in1.mm"

theorem con5VD
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> -. ps ) -> ( -. ph -> ps ) )

  proof
    wph
    wps
    wn
    #
    wb
    #
    wph
    wn
    #
    wps
    wi
    #
    @1
    @2
    @0
    wn
    #
    wi
    #
    wps
    @4
    wb
    #
    @3
    @1
    @0
    wph
    wi
    #
    @5
    @1
    @1
    @7
    @1
    idn1
    wph
    @0
    biimpr
    e1a
    @0
    wph
    con3
    e1a
    wps
    notnotb
    @6
    @3
    @5
    wps
    @4
    @2
    imbi2
    biimprcd
    e10
    in1
end
