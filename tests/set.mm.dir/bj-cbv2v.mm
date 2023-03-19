include "wal.mm"
include "wb.mm"
include "nf5ri.mm"
include "nfal.mm"
include "syl.mm"
include "nf5rd.mm"
include "bj-cbv2hv.mm"

theorem bj-cbv2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv2v.1: |- F/ x ph
  assume bj-cbv2v.2: |- F/ y ph
  assume bj-cbv2v.3: |- ( ph -> F/ y ps )
  assume bj-cbv2v.4: |- ( ph -> F/ x ch )
  assume bj-cbv2v.5: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )

  disjoint x y
  assert |- ( ph -> ( A. x ps <-> A. y ch ) )

  proof
    wph
    wph
    vy
    wal
    #
    vx
    wal
    #
    wps
    vx
    wal
    wch
    vy
    wal
    wb
    wph
    @0
    @1
    wph
    vy
    bj-cbv2v.2
    nf5ri
    @0
    vx
    wph
    vx
    vy
    bj-cbv2v.1
    nfal
    nf5ri
    syl
    wph
    wps
    wch
    vx
    vy
    wph
    wps
    vy
    bj-cbv2v.3
    nf5rd
    wph
    wch
    vx
    bj-cbv2v.4
    nf5rd
    bj-cbv2v.5
    bj-cbv2hv
    syl
end
