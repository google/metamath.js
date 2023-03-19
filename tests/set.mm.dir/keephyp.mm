include "ifboth.mm"
include "mp2an.mm"

theorem keephyp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let cA: class A
  let cB: class B
  assume keephyp.1: |- ( A = if ( ph , A , B ) -> ( ps <-> th ) )
  assume keephyp.2: |- ( B = if ( ph , A , B ) -> ( ch <-> th ) )
  assume keephyp.3: |- ps
  assume keephyp.4: |- ch


  assert |- th

  proof
    wps
    wch
    wth
    keephyp.3
    keephyp.4
    wph
    wps
    wch
    wth
    cA
    cB
    keephyp.1
    keephyp.2
    ifboth
    mp2an
end
