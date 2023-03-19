include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cnlm.mm"
include "ccom.mm"
include "clmhm.mm"
include "cnghm.mm"
include "nmhmrcl2.mm"
include "nmhmrcl1.mm"
include "anim12ci.mm"
include "nmhmlmhm.mm"
include "lmhmco.mm"
include "syl2an.mm"
include "nmhmnghm.mm"
include "nghmco.mm"
include "jca.mm"
include "isnmhm.mm"
include "sylanbrc.mm"

theorem nmhmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( T NMHom U ) /\ G e. ( S NMHom T ) ) -> ( F o. G ) e. ( S NMHom U ) )

  proof
    cF
    cT
    cU
    cnmhm
    co
    wcel
    #
    cG
    cS
    cT
    cnmhm
    co
    wcel
    #
    wa
    #
    cS
    cnlm
    wcel
    #
    cU
    cnlm
    wcel
    #
    wa
    cF
    cG
    ccom
    #
    cS
    cU
    clmhm
    co
    wcel
    #
    @5
    cS
    cU
    cnghm
    co
    wcel
    #
    wa
    @5
    cS
    cU
    cnmhm
    co
    wcel
    @0
    @4
    @1
    @3
    cT
    cU
    cF
    nmhmrcl2
    cS
    cT
    cG
    nmhmrcl1
    anim12ci
    @2
    @6
    @7
    @0
    cF
    cT
    cU
    clmhm
    co
    wcel
    cG
    cS
    cT
    clmhm
    co
    wcel
    @6
    @1
    cT
    cU
    cF
    nmhmlmhm
    cS
    cT
    cG
    nmhmlmhm
    cF
    cG
    cS
    cT
    cU
    lmhmco
    syl2an
    @0
    cF
    cT
    cU
    cnghm
    co
    wcel
    cG
    cS
    cT
    cnghm
    co
    wcel
    @7
    @1
    cT
    cU
    cF
    nmhmnghm
    cS
    cT
    cG
    nmhmnghm
    cS
    cT
    cU
    cF
    cG
    nghmco
    syl2an
    jca
    cS
    cU
    @5
    isnmhm
    sylanbrc
end
