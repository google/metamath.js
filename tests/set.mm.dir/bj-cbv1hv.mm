include "wal.mm"
include "nfa1.mm"
include "nfa2.mm"
include "wi.mm"
include "2sp.mm"
include "syl.mm"
include "nf5d.mm"
include "weq.mm"
include "bj-cbv1v.mm"

theorem bj-cbv1hv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv1hv.1: |- ( ph -> ( ps -> A. y ps ) )
  assume bj-cbv1hv.2: |- ( ph -> ( ch -> A. x ch ) )
  assume bj-cbv1hv.3: |- ( ph -> ( x = y -> ( ps -> ch ) ) )

  disjoint x y
  assert |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) )

  proof
    wph
    vy
    wal
    #
    vx
    wal
    #
    wps
    wch
    vx
    vy
    @0
    vx
    nfa1
    #
    wph
    vy
    vx
    nfa2
    #
    @1
    wps
    vy
    @3
    @1
    wph
    wps
    wps
    vy
    wal
    wi
    wph
    vx
    vy
    2sp
    #
    bj-cbv1hv.1
    syl
    nf5d
    @1
    wch
    vx
    @2
    @1
    wph
    wch
    wch
    vx
    wal
    wi
    @4
    bj-cbv1hv.2
    syl
    nf5d
    @1
    wph
    vx
    vy
    weq
    wps
    wch
    wi
    wi
    @4
    bj-cbv1hv.3
    syl
    bj-cbv1v
end
