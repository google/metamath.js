include "wal.mm"
include "wn.mm"
include "wex.mm"
include "wcel.mm"
include "wa.mm"
include "2nalexn.mm"
include "con1bii.mm"
include "nfn.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "spc2ed.mm"
include "con1d.mm"
include "syl5bir.mm"

theorem spc2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume spc2ed.x: |- F/ x ch
  assume spc2ed.y: |- F/ y ch
  assume spc2ed.1: |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ( ph /\ ( A e. V /\ B e. W ) ) -> ( A. x A. y ps -> ch ) )

  proof
    wps
    vy
    wal
    vx
    wal
    #
    wps
    wn
    #
    vy
    wex
    vx
    wex
    #
    wn
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    wa
    #
    wch
    @0
    @2
    wps
    vx
    vy
    2nalexn
    con1bii
    @3
    wch
    @2
    wph
    @1
    wch
    wn
    vx
    vy
    cA
    cB
    cV
    cW
    wch
    vx
    spc2ed.x
    nfn
    wch
    vy
    spc2ed.y
    nfn
    wph
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    wa
    wa
    wps
    wch
    spc2ed.1
    notbid
    spc2ed
    con1d
    syl5bir
end
