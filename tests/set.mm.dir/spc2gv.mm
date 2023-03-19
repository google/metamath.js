include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "spc2egv.mm"
include "2nalexn.mm"
include "syl6ibr.mm"
include "con4d.mm"

theorem spc2gv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume spc2egv.1: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( A. x A. y ph -> ps ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    wps
    wph
    vy
    wal
    vx
    wal
    #
    @0
    wps
    wn
    #
    wph
    wn
    #
    vy
    wex
    vx
    wex
    @1
    wn
    @3
    @2
    vx
    vy
    cA
    cB
    cV
    cW
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    wa
    wph
    wps
    spc2egv.1
    notbid
    spc2egv
    wph
    vx
    vy
    2nalexn
    syl6ibr
    con4d
end
