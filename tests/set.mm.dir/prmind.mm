include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "adantr.mm"
include "prmind2.mm"

theorem prmind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  assume prmind.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume prmind.2: |- ( x = y -> ( ph <-> ch ) )
  assume prmind.3: |- ( x = z -> ( ph <-> th ) )
  assume prmind.4: |- ( x = ( y x. z ) -> ( ph <-> ta ) )
  assume prmind.5: |- ( x = A -> ( ph <-> et ) )
  assume prmind.6: |- ps
  assume prmind.7: |- ( x e. Prime -> ph )
  assume prmind.8: |- ( ( y e. ( ZZ>= ` 2 ) /\ z e. ( ZZ>= ` 2 ) ) -> ( ( ch /\ th ) -> ta ) )

  disjoint x y
  disjoint A x
  disjoint x z
  disjoint ch x
  disjoint ch z
  disjoint et x
  disjoint ta x
  disjoint th x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint A n
  disjoint k n
  disjoint k z
  disjoint k ph
  disjoint n y
  disjoint n z
  disjoint n ph
  assert |- ( A e. NN -> et )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    vx
    vy
    vz
    cA
    prmind.1
    prmind.2
    prmind.3
    prmind.4
    prmind.5
    prmind.6
    vx
    cv
    #
    cprime
    wcel
    wph
    wch
    vy
    c1
    @0
    c1
    cmin
    co
    cfz
    co
    wral
    prmind.7
    adantr
    prmind.8
    prmind2
end
