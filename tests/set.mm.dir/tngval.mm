include "wcel.mm"
include "wa.mm"
include "ctng.mm"
include "co.mm"
include "cnx.mm"
include "cds.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cts.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "csg.mm"
include "ccom.mm"
include "cmopn.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "coeq12d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-tng.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem tngval
  let cD: class D
  let cT: class T
  let cG: class G
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  assume tngval.t: |- T = ( G toNrmGrp N )
  assume tngval.m: |- .- = ( -g ` G )
  assume tngval.d: |- D = ( N o. .- )
  assume tngval.j: |- J = ( MetOpen ` D )


  assert |- ( ( G e. V /\ N e. W ) -> T = ( ( G sSet <. ( dist ` ndx ) , D >. ) sSet <. ( TopSet ` ndx ) , J >. ) )

  proof
    cG
    cV
    wcel
    #
    cN
    cW
    wcel
    #
    wa
    cT
    cG
    cN
    ctng
    co
    #
    cG
    cnx
    cds
    cfv
    #
    cD
    cop
    #
    csts
    co
    #
    cnx
    cts
    cfv
    #
    cJ
    cop
    #
    csts
    co
    #
    tngval.t
    @0
    cG
    cvv
    wcel
    cN
    cvv
    wcel
    @2
    @8
    wceq
    @1
    cG
    cV
    elex
    cN
    cW
    elex
    vg
    vf
    cG
    cN
    cvv
    cvv
    vg
    cv
    #
    @3
    vf
    cv
    #
    @9
    csg
    cfv
    #
    ccom
    #
    cop
    #
    csts
    co
    #
    @6
    @12
    cmopn
    cfv
    #
    cop
    #
    csts
    co
    @8
    ctng
    @9
    cG
    wceq
    #
    @10
    cN
    wceq
    #
    wa
    #
    @14
    @5
    @16
    @7
    csts
    @19
    @9
    cG
    @13
    @4
    csts
    @17
    @18
    simpl
    #
    @19
    @12
    cD
    @3
    @19
    @12
    cN
    c.mi
    ccom
    cD
    @19
    @10
    cN
    @11
    c.mi
    @17
    @18
    simpr
    @19
    @11
    cG
    csg
    cfv
    c.mi
    @19
    @9
    cG
    csg
    @20
    fveq2d
    tngval.m
    syl6eqr
    coeq12d
    tngval.d
    syl6eqr
    #
    opeq2d
    oveq12d
    @19
    @15
    cJ
    @6
    @19
    @15
    cD
    cmopn
    cfv
    cJ
    @19
    @12
    cD
    cmopn
    @21
    fveq2d
    tngval.j
    syl6eqr
    opeq2d
    oveq12d
    vf
    vg
    df-tng
    @5
    @7
    csts
    ovex
    ovmpt2a
    syl2an
    syl5eq
end
