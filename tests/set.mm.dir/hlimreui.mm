include "cv.mm"
include "chli.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "hlimuni.mm"
include "rgen2w.mm"
include "biantru.mm"
include "breq2.mm"
include "reu4.mm"
include "bitr4i.mm"

theorem hlimreui
  let vx: setvar x
  let cF: class F
  let cH: class H
  let vy: setvar y

  disjoint F x
  disjoint H x
  disjoint x y
  disjoint F y
  disjoint H y
  assert |- ( E. x e. H F ~~>v x <-> E! x e. H F ~~>v x )

  proof
    cF
    vx
    cv
    #
    chli
    wbr
    #
    vx
    cH
    wrex
    #
    @2
    @1
    cF
    vy
    cv
    #
    chli
    wbr
    #
    wa
    vx
    vy
    weq
    wi
    #
    vy
    cH
    wral
    vx
    cH
    wral
    #
    wa
    @1
    vx
    cH
    wreu
    @6
    @2
    @5
    vx
    vy
    cH
    cH
    @0
    @3
    cF
    hlimuni
    rgen2w
    biantru
    @1
    @4
    vx
    vy
    cH
    @0
    @3
    cF
    chli
    breq2
    reu4
    bitr4i
end
