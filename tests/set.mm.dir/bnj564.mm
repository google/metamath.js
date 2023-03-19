include "cv.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "simp1bi.mm"
include "fndm.mm"
include "syl.mm"

theorem bnj564
  let wta: wff ta
  let vf: setvar f
  let vm: setvar m
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj564.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )


  assert |- ( ta -> dom f = m )

  proof
    wta
    vf
    cv
    #
    vm
    cv
    #
    wfn
    #
    @0
    cdm
    @1
    wceq
    wta
    @2
    bnjwphm
    bnjwpsm
    bnj564.17
    simp1bi
    @1
    @0
    fndm
    syl
end
