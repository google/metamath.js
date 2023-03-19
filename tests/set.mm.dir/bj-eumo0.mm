include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "euf.mm"
include "biimp.mm"
include "alimi.mm"
include "eximi.mm"
include "sylbi.mm"

theorem bj-eumo0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume bj-eumo0.1: |- F/ y ph

  disjoint x y
  assert |- ( E! x ph -> E. y A. x ( ph -> x = y ) )

  proof
    wph
    vx
    weu
    wph
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    @0
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    vy
    bj-eumo0.1
    euf
    @2
    @4
    vy
    @1
    @3
    vx
    wph
    @0
    biimp
    alimi
    eximi
    sylbi
end
