include "cv.mm"
include "wf.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "cfv.mm"
include "wceq.mm"
include "notbid.mm"
include "ac6s.mm"
include "con3i.mm"
include "dfrex2.mm"
include "imbi2i.mm"
include "albii.mm"
include "alinexa.mm"
include "bitri.mm"
include "dfral2.mm"
include "rexbii.mm"
include "rexnal.mm"
include "3imtr4i.mm"

theorem ac6n
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vz: setvar z
  assume ac6s.1: |- A e. _V
  assume ac6s.2: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A x
  disjoint A f
  disjoint x y
  disjoint B x
  disjoint f y
  disjoint B y
  disjoint B f
  disjoint f ph
  disjoint ps y
  disjoint x z
  disjoint f z
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( A. f ( f : A --> B -> E. x e. A ps ) -> E. x e. A A. y e. B ph )

  proof
    cA
    cB
    vf
    cv
    #
    wf
    #
    wps
    wn
    #
    vx
    cA
    wral
    #
    wa
    vf
    wex
    #
    wn
    #
    wph
    wn
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wn
    #
    @1
    wps
    vx
    cA
    wrex
    #
    wi
    #
    vf
    wal
    #
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wrex
    #
    @8
    @4
    @6
    @2
    vx
    vy
    cA
    cB
    vf
    ac6s.1
    vy
    cv
    vx
    cv
    @0
    cfv
    wceq
    wph
    wps
    ac6s.2
    notbid
    ac6s
    con3i
    @12
    @1
    @3
    wn
    #
    wi
    #
    vf
    wal
    @5
    @11
    @16
    vf
    @10
    @15
    @1
    wps
    vx
    cA
    dfrex2
    imbi2i
    albii
    @1
    @3
    vf
    alinexa
    bitri
    @14
    @7
    wn
    #
    vx
    cA
    wrex
    @9
    @13
    @17
    vx
    cA
    wph
    vy
    cB
    dfral2
    rexbii
    @7
    vx
    cA
    rexnal
    bitri
    3imtr4i
end
