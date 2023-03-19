include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "isseti.mm"
include "vex.mm"
include "ac6s6.mm"
include "pm3.2i.mm"
include "exan.mm"
include "exdistr.mm"
include "mpbir.mm"
include "nfcv.mm"
include "raleqf.mm"
include "biimpa.mm"
include "2eximi.mm"
include "ax5e.mm"
include "mp2b.mm"

theorem ac6s6f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vz: setvar z
  assume ac6s6f.1: |- A e. _V
  assume ac6s6f.2: |- F/ y ps
  assume ac6s6f.3: |- ( y = ( f ` x ) -> ( ph <-> ps ) )
  assume ac6s6f.4: |- F/_ x A

  disjoint f ph
  disjoint x y
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint ph z
  disjoint ps z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f z
  assert |- E. f A. x e. A ( E. y ph -> ps )

  proof
    vz
    cv
    #
    cA
    wceq
    #
    wph
    vy
    wex
    wps
    wi
    #
    vx
    @0
    wral
    #
    wa
    #
    vf
    wex
    vz
    wex
    #
    @2
    vx
    cA
    wral
    #
    vf
    wex
    #
    vz
    wex
    @7
    @5
    @1
    @3
    vf
    wex
    #
    wa
    vz
    wex
    @1
    @8
    vz
    @1
    vz
    wex
    @8
    vz
    cA
    ac6s6f.1
    isseti
    wph
    wps
    vx
    vy
    @0
    vf
    ac6s6f.2
    vz
    vex
    ac6s6f.3
    ac6s6
    pm3.2i
    exan
    @1
    @3
    vz
    vf
    exdistr
    mpbir
    @4
    @6
    vz
    vf
    @1
    @3
    @6
    @2
    vx
    @0
    cA
    vx
    @0
    nfcv
    ac6s6f.4
    raleqf
    biimpa
    2eximi
    @7
    vz
    ax5e
    mp2b
end
