include "wn.mm"
include "wal.mm"
include "wi.mm"
include "wex.mm"
include "2nexaln.mm"
include "imbi12i.mm"
include "con4.mm"
include "sylbir.mm"

theorem bj-alcomexcom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A. x A. y -. ph -> A. y A. x -. ph ) -> ( E. y E. x ph -> E. x E. y ph ) )

  proof
    wph
    wn
    #
    vy
    wal
    vx
    wal
    #
    @0
    vx
    wal
    vy
    wal
    #
    wi
    wph
    vy
    wex
    vx
    wex
    #
    wn
    #
    wph
    vx
    wex
    vy
    wex
    #
    wn
    #
    wi
    @5
    @3
    wi
    @4
    @1
    @6
    @2
    wph
    vx
    vy
    2nexaln
    wph
    vy
    vx
    2nexaln
    imbi12i
    @3
    @5
    con4
    sylbir
end
