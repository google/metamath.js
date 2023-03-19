include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "ccom.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "rhmrcl2.mm"
include "rhmrcl1.mm"
include "anim12ci.mm"
include "rhmghm.mm"
include "ghmco.mm"
include "syl2an.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "mhmco.mm"
include "jca.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem rhmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( T RingHom U ) /\ G e. ( S RingHom T ) ) -> ( F o. G ) e. ( S RingHom U ) )

  proof
    cF
    cT
    cU
    crh
    co
    wcel
    #
    cG
    cS
    cT
    crh
    co
    wcel
    #
    wa
    #
    cS
    crg
    wcel
    #
    cU
    crg
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
    @5
    cS
    cmgp
    cfv
    #
    cU
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    @5
    cS
    cU
    crh
    co
    wcel
    @0
    @4
    @1
    @3
    cT
    cU
    cF
    rhmrcl2
    cS
    cT
    cG
    rhmrcl1
    anim12ci
    @2
    @6
    @9
    @0
    cF
    cT
    cU
    cghm
    co
    wcel
    cG
    cS
    cT
    cghm
    co
    wcel
    @6
    @1
    cT
    cU
    cF
    rhmghm
    cS
    cT
    cG
    rhmghm
    cS
    cT
    cU
    cF
    cG
    ghmco
    syl2an
    @0
    cF
    cT
    cmgp
    cfv
    #
    @8
    cmhm
    co
    wcel
    cG
    @7
    @10
    cmhm
    co
    wcel
    @9
    @1
    cT
    cU
    cF
    @10
    @8
    @10
    eqid
    #
    @8
    eqid
    #
    rhmmhm
    cS
    cT
    cG
    @7
    @10
    @7
    eqid
    #
    @11
    rhmmhm
    @7
    @10
    @8
    cF
    cG
    mhmco
    syl2an
    jca
    cS
    cU
    @5
    @7
    @8
    @13
    @12
    isrhm
    sylanbrc
end
