include "cho.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "cch.mm"
include "chio.mm"
include "cif.mm"
include "rneq.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "id.mm"
include "coeq12d.mm"
include "eqeq12d.mm"
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
include "hmopidmchi.mm"
include "dedth.mm"

theorem hmopidmch
  let cT: class T


  assert |- ( ( T e. HrmOp /\ ( T o. T ) = T ) -> ran T e. CH )

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
    crn
    #
    cch
    wcel
    @3
    cT
    chio
    cif
    #
    crn
    #
    cch
    wcel
    cT
    chio
    cT
    @5
    wceq
    #
    @4
    @6
    cch
    cT
    @5
    rneq
    eleq1d
    @5
    @5
    cho
    wcel
    #
    @5
    @5
    ccom
    #
    @5
    wceq
    #
    @3
    @8
    @10
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
    @7
    @0
    @8
    @2
    @10
    cT
    @5
    cho
    eleq1
    @7
    @1
    @9
    cT
    @5
    @7
    cT
    @5
    cT
    @5
    @7
    id
    #
    @14
    coeq12d
    @14
    eqeq12d
    anbi12d
    chio
    @5
    wceq
    #
    @11
    @8
    @13
    @10
    chio
    @5
    cho
    eleq1
    @15
    @12
    @9
    chio
    @5
    @15
    chio
    @5
    chio
    @5
    @15
    id
    #
    @16
    coeq12d
    @16
    eqeq12d
    anbi12d
    @11
    @13
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
    @8
    @10
    @17
    simpri
    hmopidmchi
    dedth
end
