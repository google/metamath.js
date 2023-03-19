include "chil.mm"
include "wf.mm"
include "wa.mm"
include "chos.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cva.mm"
include "cmpt.mm"
include "wcel.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "adantll.mm"
include "hvaddcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "hosmval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem hoaddcl
  let cS: class S
  let cT: class T
  let cA: class A
  let vx: setvar x


  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( S +op T ) : ~H --> ~H )

  proof
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    chil
    chil
    cS
    cT
    chos
    co
    #
    wf
    chil
    chil
    vx
    chil
    vx
    cv
    #
    cS
    cfv
    #
    @4
    cT
    cfv
    #
    cva
    co
    #
    cmpt
    #
    wf
    @2
    vx
    chil
    @7
    chil
    @8
    @2
    @4
    chil
    wcel
    #
    wa
    @5
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @7
    chil
    wcel
    @0
    @9
    @10
    @1
    chil
    chil
    @4
    cS
    ffvelrn
    adantlr
    @1
    @9
    @11
    @0
    chil
    chil
    @4
    cT
    ffvelrn
    adantll
    @5
    @6
    hvaddcl
    syl2anc
    @8
    eqid
    fmptd
    @2
    chil
    chil
    @3
    @8
    vx
    cS
    cT
    hosmval
    feq1d
    mpbird
end
