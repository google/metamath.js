include "c0.mm"
include "copab.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "nfopab1.mm"
include "nfel2.mm"
include "nfn.mm"
include "nfopab2.mm"
include "wne.mm"
include "wi.mm"
include "vex.mm"
include "opnzi.mm"
include "nesym.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "adantr.mm"
include "exlimi.mm"
include "id.mm"
include "pm2.61i.mm"

theorem 0neqopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- -. (/) e. { <. x , y >. | ph }

  proof
    c0
    wph
    vx
    vy
    copab
    #
    wcel
    #
    @1
    wn
    #
    @1
    c0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    @2
    wph
    vx
    vy
    c0
    elopab
    @8
    @2
    vx
    @1
    vx
    vx
    c0
    @0
    wph
    vx
    vy
    nfopab1
    nfel2
    nfn
    @7
    @2
    vy
    @1
    vy
    vy
    c0
    @0
    wph
    vx
    vy
    nfopab2
    nfel2
    nfn
    @6
    @2
    wph
    @5
    c0
    wne
    #
    @6
    @2
    wi
    #
    @3
    @4
    vx
    vex
    vy
    vex
    opnzi
    @9
    @6
    wn
    @10
    @5
    c0
    nesym
    @6
    @2
    pm2.21
    sylbi
    ax-mp
    adantr
    exlimi
    exlimi
    sylbi
    @2
    id
    pm2.61i
end
