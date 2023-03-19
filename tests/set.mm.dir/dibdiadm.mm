include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "wceq.mm"
include "dibfna.mm"
include "fndm.mm"
include "syl.mm"

theorem dibdiadm
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vf: setvar f
  assume dibfna.h: |- H = ( LHyp ` K )
  assume dibfna.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibfna.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( K e. V /\ W e. H ) -> dom I = dom J )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cI
    cJ
    cdm
    #
    wfn
    cI
    cdm
    @0
    wceq
    cH
    cI
    cJ
    cK
    cV
    cW
    dibfna.h
    dibfna.j
    dibfna.i
    dibfna
    @0
    cI
    fndm
    syl
end
