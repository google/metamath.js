include "wn.mm"
include "w3o.mm"
include "wo.mm"
include "3orel3.mm"
include "orel1.mm"
include "sylan9r.mm"

theorem 3orel13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( -. ph /\ -. ch ) -> ( ( ph \/ ps \/ ch ) -> ps ) )

  proof
    wch
    wn
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    wph
    wn
    wps
    wph
    wps
    wch
    3orel3
    wph
    wps
    orel1
    sylan9r
end
