include "wmo.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wa.mm"
include "nfa1.mm"
include "nfe1.mm"
include "nfmo.mm"
include "wi.mm"
include "nfex.mm"
include "copsexg.mm"
include "mobidv.mm"
include "biimpcd.mm"
include "sps.mm"
include "exlimd.mm"
include "wn.mm"
include "simpl.mm"
include "2eximi.mm"
include "exlimiv.mm"
include "con3i.mm"
include "exmo.mm"
include "ori.mm"
include "syl.mm"
include "pm2.61d1.mm"

theorem mosubopt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A. y A. z E* x ph -> E* x E. y E. z ( A = <. y , z >. /\ ph ) )

  proof
    wph
    vx
    wmo
    #
    vz
    wal
    #
    vy
    wal
    #
    cA
    vy
    cv
    vz
    cv
    cop
    wceq
    #
    vz
    wex
    #
    vy
    wex
    #
    @3
    wph
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wmo
    #
    @2
    @4
    @9
    vy
    @1
    vy
    nfa1
    @8
    vy
    vx
    @7
    vy
    nfe1
    nfmo
    @1
    @4
    @9
    wi
    vy
    @1
    @3
    @9
    vz
    @0
    vz
    nfa1
    @8
    vz
    vx
    @7
    vz
    vy
    @6
    vz
    nfe1
    nfex
    nfmo
    @0
    @3
    @9
    wi
    vz
    @3
    @0
    @9
    @3
    wph
    @8
    vx
    wph
    vy
    vz
    cA
    copsexg
    mobidv
    biimpcd
    sps
    exlimd
    sps
    exlimd
    @5
    wn
    @8
    vx
    wex
    #
    wn
    @9
    @10
    @5
    @8
    @5
    vx
    @6
    @3
    vy
    vz
    @3
    wph
    simpl
    2eximi
    exlimiv
    con3i
    @10
    @9
    @8
    vx
    exmo
    ori
    syl
    pm2.61d1
end
