include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "cdm.mm"
include "wceq.mm"
include "dihfn.mm"
include "fndm.mm"
include "syl.mm"

theorem dihdm
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dihfn.b: |- B = ( Base ` K )
  assume dihfn.h: |- H = ( LHyp ` K )
  assume dihfn.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> dom I = B )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cI
    cB
    wfn
    cI
    cdm
    cB
    wceq
    cB
    cH
    cI
    cK
    cW
    dihfn.b
    dihfn.h
    dihfn.i
    dihfn
    cB
    cI
    fndm
    syl
end
