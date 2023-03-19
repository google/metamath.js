include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cho.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cch.mm"
include "cfv.mm"
include "dfpjop.mm"
include "hmopidmch.mm"
include "hmopidmpj.mm"
include "jca.mm"
include "sylbi.mm"

theorem elpjch
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( T e. ran projh -> ( ran T e. CH /\ T = ( projh ` ran T ) ) )

  proof
    cT
    cpjh
    crn
    wcel
    cT
    cho
    wcel
    cT
    cT
    ccom
    cT
    wceq
    wa
    #
    cT
    crn
    #
    cch
    wcel
    #
    cT
    @1
    cpjh
    cfv
    wceq
    #
    wa
    cT
    dfpjop
    @0
    @2
    @3
    cT
    hmopidmch
    cT
    hmopidmpj
    jca
    sylbi
end
