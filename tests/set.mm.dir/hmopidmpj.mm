include "cho.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "cpjh.mm"
include "cfv.mm"
include "chio.mm"
include "cif.mm"
include "id.mm"
include "rneq.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "eleq1.mm"
include "coeq12d.mm"
include "anbi12d.mm"
include "idhmop.mm"
include "chil.mm"
include "wf1o.mm"
include "wf.mm"
include "hoif.mm"
include "f1of.mm"
include "ax-mp.mm"
include "hoid1i.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "simpli.mm"
include "simpri.mm"
include "hmopidmpji.mm"
include "dedth.mm"

theorem hmopidmpj
  let cT: class T


  assert |- ( ( T e. HrmOp /\ ( T o. T ) = T ) -> T = ( projh ` ran T ) )

  proof
    cT
    cho
    wcel
    #
    cT
    cT
    ccom
    #
    cT
    wceq
    #
    wa
    #
    cT
    cT
    crn
    #
    cpjh
    cfv
    #
    wceq
    @3
    cT
    chio
    cif
    #
    @6
    crn
    #
    cpjh
    cfv
    #
    wceq
    cT
    chio
    cT
    @6
    wceq
    #
    cT
    @6
    @5
    @8
    @9
    id
    #
    @9
    @4
    @7
    cpjh
    cT
    @6
    rneq
    fveq2d
    eqeq12d
    @6
    @6
    cho
    wcel
    #
    @6
    @6
    ccom
    #
    @6
    wceq
    #
    @3
    @11
    @13
    wa
    chio
    cho
    wcel
    #
    chio
    chio
    ccom
    #
    chio
    wceq
    #
    wa
    cT
    chio
    @9
    @0
    @11
    @2
    @13
    cT
    @6
    cho
    eleq1
    @9
    @1
    @12
    cT
    @6
    @9
    cT
    @6
    cT
    @6
    @10
    @10
    coeq12d
    @10
    eqeq12d
    anbi12d
    chio
    @6
    wceq
    #
    @14
    @11
    @16
    @13
    chio
    @6
    cho
    eleq1
    @17
    @15
    @12
    chio
    @6
    @17
    chio
    @6
    chio
    @6
    @17
    id
    #
    @18
    coeq12d
    @18
    eqeq12d
    anbi12d
    @14
    @16
    idhmop
    chio
    chil
    chil
    chio
    wf1o
    chil
    chil
    chio
    wf
    hoif
    chil
    chil
    chio
    f1of
    ax-mp
    hoid1i
    pm3.2i
    elimhyp
    #
    simpli
    @11
    @13
    @19
    simpri
    hmopidmpji
    dedth
end
