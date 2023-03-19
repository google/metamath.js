include "cop.mm"
include "co.mm"
include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "cco.mm"
include "cfv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "comffval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem comffn
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  assume comfffn.o: |- O = ( comf ` C )
  assume comfffn.b: |- B = ( Base ` C )
  assume comffn.h: |- H = ( Hom ` C )
  assume comffn.x: |- ( ph -> X e. B )
  assume comffn.y: |- ( ph -> Y e. B )
  assume comffn.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( <. X , Y >. O Z ) Fn ( ( Y H Z ) X. ( X H Y ) ) )

  proof
    wph
    cX
    cY
    cop
    #
    cZ
    cO
    co
    #
    cY
    cZ
    cH
    co
    #
    cX
    cY
    cH
    co
    #
    cxp
    #
    wfn
    vg
    vf
    @2
    @3
    vg
    cv
    #
    vf
    cv
    #
    @0
    cZ
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt2
    #
    @4
    wfn
    vg
    vf
    @2
    @3
    @9
    @10
    @10
    eqid
    @5
    @6
    @8
    ovex
    fnmpt2i
    wph
    @4
    @1
    @10
    wph
    cB
    cC
    @7
    vf
    vg
    cH
    cO
    cX
    cY
    cZ
    comfffn.o
    comfffn.b
    comffn.h
    @7
    eqid
    comffn.x
    comffn.y
    comffn.z
    comffval
    fneq1d
    mpbiri
end
