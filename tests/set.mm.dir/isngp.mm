include "cgrp.mm"
include "cmt.mm"
include "cin.mm"
include "wcel.mm"
include "ccom.mm"
include "wss.mm"
include "wa.mm"
include "cngp.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cv.mm"
include "cnm.mm"
include "cfv.mm"
include "csg.mm"
include "cds.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "df-ngp.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem isngp
  let cD: class D
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume isngp.n: |- N = ( norm ` G )
  assume isngp.z: |- .- = ( -g ` G )
  assume isngp.d: |- D = ( dist ` G )


  assert |- ( G e. NrmGrp <-> ( G e. Grp /\ G e. MetSp /\ ( N o. .- ) C_ D ) )

  proof
    cG
    cgrp
    cmt
    cin
    #
    wcel
    #
    cN
    c.mi
    ccom
    #
    cD
    wss
    #
    wa
    cG
    cgrp
    wcel
    #
    cG
    cmt
    wcel
    #
    wa
    #
    @3
    wa
    cG
    cngp
    wcel
    @4
    @5
    @3
    w3a
    @1
    @6
    @3
    cG
    cgrp
    cmt
    elin
    anbi1i
    vg
    cv
    #
    cnm
    cfv
    #
    @7
    csg
    cfv
    #
    ccom
    #
    @7
    cds
    cfv
    #
    wss
    @3
    vg
    cG
    @0
    cngp
    @7
    cG
    wceq
    #
    @10
    @2
    @11
    cD
    @12
    @8
    cN
    @9
    c.mi
    @12
    @8
    cG
    cnm
    cfv
    cN
    @7
    cG
    cnm
    fveq2
    isngp.n
    syl6eqr
    @12
    @9
    cG
    csg
    cfv
    c.mi
    @7
    cG
    csg
    fveq2
    isngp.z
    syl6eqr
    coeq12d
    @12
    @11
    cG
    cds
    cfv
    cD
    @7
    cG
    cds
    fveq2
    isngp.d
    syl6eqr
    sseq12d
    vg
    df-ngp
    elrab2
    @4
    @5
    @3
    df-3an
    3bitr4i
end
