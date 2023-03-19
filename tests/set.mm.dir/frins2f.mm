include "wfr.mm"
include "wse.mm"
include "wral.mm"
include "frins2fg.mm"
include "mp2an.mm"
include "rspec.mm"

theorem frins2f
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume frins2f.1: |- R Fr A
  assume frins2f.2: |- R Se A
  assume frins2f.3: |- F/ y ps
  assume frins2f.4: |- ( y = z -> ( ph <-> ps ) )
  assume frins2f.5: |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint R y
  disjoint R z
  assert |- ( y e. A -> ph )

  proof
    wph
    vy
    cA
    cA
    cR
    wfr
    cA
    cR
    wse
    wph
    vy
    cA
    wral
    frins2f.1
    frins2f.2
    wph
    wps
    vy
    vz
    cA
    cR
    frins2f.5
    frins2f.3
    frins2f.4
    frins2fg
    mp2an
    rspec
end
