include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cghm.mm"
include "ccnv.mm"
include "isgim2.mm"
include "ghmco.mm"
include "cnvco.mm"
include "ancoms.mm"
include "syl5eqel.mm"
include "anim12i.mm"
include "an4s.mm"
include "syl2anb.mm"
include "sylibr.mm"

theorem gimco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( T GrpIso U ) /\ G e. ( S GrpIso T ) ) -> ( F o. G ) e. ( S GrpIso U ) )

  proof
    cF
    cT
    cU
    cgim
    co
    wcel
    #
    cG
    cS
    cT
    cgim
    co
    wcel
    #
    wa
    cF
    cG
    ccom
    #
    cS
    cU
    cghm
    co
    wcel
    #
    @2
    ccnv
    #
    cU
    cS
    cghm
    co
    #
    wcel
    #
    wa
    #
    @2
    cS
    cU
    cgim
    co
    wcel
    @0
    cF
    cT
    cU
    cghm
    co
    wcel
    #
    cF
    ccnv
    #
    cU
    cT
    cghm
    co
    wcel
    #
    wa
    cG
    cS
    cT
    cghm
    co
    wcel
    #
    cG
    ccnv
    #
    cT
    cS
    cghm
    co
    wcel
    #
    wa
    @7
    @1
    cT
    cU
    cF
    isgim2
    cS
    cT
    cG
    isgim2
    @8
    @11
    @10
    @13
    @7
    @8
    @11
    wa
    @3
    @10
    @13
    wa
    #
    @6
    cS
    cT
    cU
    cF
    cG
    ghmco
    @14
    @4
    @12
    @9
    ccom
    #
    @5
    cF
    cG
    cnvco
    @13
    @10
    @15
    @5
    wcel
    cU
    cT
    cS
    @12
    @9
    ghmco
    ancoms
    syl5eqel
    anim12i
    an4s
    syl2anb
    cS
    cU
    @2
    isgim2
    sylibr
end
