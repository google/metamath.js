include "wa.mm"
include "simpll.mm"
include "wn.mm"
include "simplr.mm"
include "ifbothda.mm"

theorem ifboth
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let cA: class A
  let cB: class B
  assume ifboth.1: |- ( A = if ( ph , A , B ) -> ( ps <-> th ) )
  assume ifboth.2: |- ( B = if ( ph , A , B ) -> ( ch <-> th ) )


  assert |- ( ( ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wps
    wch
    wa
    cA
    cB
    ifboth.1
    ifboth.2
    wps
    wch
    wph
    simpll
    wps
    wch
    wph
    wn
    simplr
    ifbothda
end
