include "wi.mm"
include "wn.mm"
include "idn1.mm"
include "idn2.mm"
include "notnotr.mm"
include "e2.mm"
include "id.mm"
include "e12.mm"
include "notnot.mm"
include "in2.mm"
include "con4.mm"
include "e1a.mm"
include "in1.mm"

theorem con3ALTVD
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) )

  proof
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
    #
    @0
    @2
    wn
    #
    @1
    wn
    #
    wi
    @3
    @0
    @4
    @5
    @0
    @4
    wps
    @5
    @0
    @0
    @4
    wph
    wps
    @0
    idn1
    @0
    @4
    @4
    wph
    @0
    @4
    idn2
    wph
    notnotr
    e2
    @0
    id
    e12
    wps
    notnot
    e2
    in2
    @2
    @1
    con4
    e1a
    in1
end
