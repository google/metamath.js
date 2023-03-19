include "wn.mm"
include "w3a.mm"
include "w3o.mm"
include "3ioran.mm"
include "con1bii.mm"
include "bicomi.mm"

theorem 3oran
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ps \/ ch ) <-> -. ( -. ph /\ -. ps /\ -. ch ) )

  proof
    wph
    wn
    wps
    wn
    wch
    wn
    w3a
    #
    wn
    wph
    wps
    wch
    w3o
    #
    @1
    @0
    wph
    wps
    wch
    3ioran
    con1bii
    bicomi
end
