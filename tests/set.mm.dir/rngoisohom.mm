include "crngo.mm"
include "wcel.mm"
include "crngiso.mm"
include "co.mm"
include "crnghom.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "wf1o.mm"
include "eqid.mm"
include "isrngoiso.mm"
include "simprbda.mm"
include "3impa.mm"

theorem rngoisohom
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngIso S ) ) -> F e. ( R RngHom S ) )

  proof
    cR
    crngo
    wcel
    #
    cS
    crngo
    wcel
    #
    cF
    cR
    cS
    crngiso
    co
    wcel
    #
    cF
    cR
    cS
    crnghom
    co
    wcel
    #
    @0
    @1
    wa
    @2
    @3
    cR
    c1st
    cfv
    #
    crn
    #
    cS
    c1st
    cfv
    #
    crn
    #
    cF
    wf1o
    cR
    cS
    cF
    @4
    @6
    @5
    @7
    @4
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    isrngoiso
    simprbda
    3impa
end
