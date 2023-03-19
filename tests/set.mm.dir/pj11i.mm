include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "crn.mm"
include "rneq.mm"
include "pjrni.mm"
include "3eqtr3g.mm"
include "fveq2.mm"
include "impbii.mm"

theorem pj11i
  let cG: class G
  let cH: class H
  assume pjsumt.1: |- G e. CH
  assume pjsumt.2: |- H e. CH


  assert |- ( ( projh ` G ) = ( projh ` H ) <-> G = H )

  proof
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    wceq
    #
    cG
    cH
    wceq
    @2
    @0
    crn
    @1
    crn
    cG
    cH
    @0
    @1
    rneq
    cG
    pjsumt.1
    pjrni
    cH
    pjsumt.2
    pjrni
    3eqtr3g
    cG
    cH
    cpjh
    fveq2
    impbii
end
