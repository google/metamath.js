include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "csg.mm"
include "eqidd.mm"
include "wcel.mm"
include "wa.mm"
include "oveqdr.mm"
include "grpinvpropd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "eqid.mm"
include "grpsubfval.mm"
include "3eqtr4g.mm"

theorem grpsubpropd
  let wph: wff ph
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume grpsubpropd.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume grpsubpropd.p: |- ( ph -> ( +g ` G ) = ( +g ` H ) )


  assert |- ( ph -> ( -g ` G ) = ( -g ` H ) )

  proof
    wph
    va
    vb
    cG
    cbs
    cfv
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    va
    vb
    cH
    cbs
    cfv
    #
    @7
    @1
    @2
    cH
    cminusg
    cfv
    #
    cfv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    cmpt2
    cG
    csg
    cfv
    #
    cH
    csg
    cfv
    #
    wph
    va
    vb
    @0
    @0
    @6
    @7
    @7
    @11
    grpsubpropd.b
    grpsubpropd.b
    wph
    @1
    @1
    @4
    @9
    @5
    @10
    grpsubpropd.p
    wph
    @1
    eqidd
    wph
    @2
    @3
    @8
    wph
    vx
    vy
    @0
    cG
    cH
    wph
    @0
    eqidd
    grpsubpropd.b
    wph
    vx
    cv
    @0
    wcel
    vy
    cv
    @0
    wcel
    wa
    vx
    vy
    @5
    @10
    grpsubpropd.p
    oveqdr
    grpinvpropd
    fveq1d
    oveq123d
    mpt2eq123dv
    va
    vb
    @0
    @5
    cG
    @3
    @12
    @0
    eqid
    @5
    eqid
    @3
    eqid
    @12
    eqid
    grpsubfval
    va
    vb
    @7
    @10
    cH
    @8
    @13
    @7
    eqid
    @10
    eqid
    @8
    eqid
    @13
    eqid
    grpsubfval
    3eqtr4g
end
