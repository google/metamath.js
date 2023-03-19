include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "chom.mm"
include "co.mm"
include "cco.mm"
include "cmpt2.mm"
include "eqid.mm"
include "comfffval.mm"
include "ovex.mm"
include "fvex.mm"
include "mpt2ex.mm"
include "fnmpt2i.mm"

theorem comfffn
  let cB: class B
  let cC: class C
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let wph: wff ph
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume comfffn.o: |- O = ( comf ` C )
  assume comfffn.b: |- B = ( Base ` C )


  assert |- O Fn ( ( B X. B ) X. B )

  proof
    vx
    vy
    cB
    cB
    cxp
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    @0
    @3
    cfv
    #
    vg
    cv
    vf
    cv
    @0
    @2
    cC
    cco
    cfv
    #
    co
    co
    #
    cmpt2
    cO
    vx
    vy
    cB
    cC
    @6
    vf
    vg
    @3
    cO
    comfffn.o
    comfffn.b
    @3
    eqid
    @6
    eqid
    comfffval
    vg
    vf
    @4
    @5
    @7
    @1
    @2
    @3
    ovex
    @0
    @3
    fvex
    mpt2ex
    fnmpt2i
end
