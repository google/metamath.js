include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "wceq.mm"
include "tendof.mm"
include "fcoi1.mm"
include "syl.mm"

theorem tendo1mulr
  let cT: class T
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let cS: class S
  let cV: class V
  let cF: class F
  let cG: class G
  assume tendof.h: |- H = ( LHyp ` K )
  assume tendof.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendof.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ U e. E ) -> ( U o. ( _I |` T ) ) = U )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cU
    cE
    wcel
    wa
    cT
    cT
    cU
    wf
    cU
    cid
    cT
    cres
    ccom
    cU
    wceq
    cU
    cT
    cE
    cH
    cK
    chlt
    cW
    tendof.h
    tendof.t
    tendof.e
    tendof
    cT
    cT
    cU
    fcoi1
    syl
end
