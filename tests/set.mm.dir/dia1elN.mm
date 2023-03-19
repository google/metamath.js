include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "crn.mm"
include "dia1N.mm"
include "wfun.mm"
include "cdm.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "f1ofun.mm"
include "syl.mm"
include "dia1eldmN.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem dia1elN
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume dia1.h: |- H = ( LHyp ` K )
  assume dia1.t: |- T = ( ( LTrn ` K ) ` W )
  assume dia1.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> T e. ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cW
    cI
    cfv
    #
    cT
    cI
    crn
    #
    cT
    cH
    cI
    cK
    cW
    dia1.h
    dia1.t
    dia1.i
    dia1N
    @0
    cI
    wfun
    #
    cW
    cI
    cdm
    #
    wcel
    @1
    @2
    wcel
    @0
    @4
    @2
    cI
    wf1o
    @3
    cH
    cI
    cK
    cW
    dia1.h
    dia1.i
    diaf11N
    @4
    @2
    cI
    f1ofun
    syl
    cH
    cI
    cK
    cW
    dia1.h
    dia1.i
    dia1eldmN
    cW
    cI
    fvelrn
    syl2anc
    eqeltrrd
end
