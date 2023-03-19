include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "crng.mm"
include "ccom.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgmhm.mm"
include "rnghmrcl.mm"
include "simprd.mm"
include "simpld.mm"
include "anim12ci.mm"
include "rnghmghm.mm"
include "ghmco.mm"
include "syl2an.mm"
include "eqid.mm"
include "rnghmmgmhm.mm"
include "mgmhmco.mm"
include "jca.mm"
include "isrnghmmul.mm"
include "sylanbrc.mm"

theorem rnghmco
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F e. ( T RngHomo U ) /\ G e. ( S RngHomo T ) ) -> ( F o. G ) e. ( S RngHomo U ) )

  proof
    cF
    cT
    cU
    crngh
    co
    wcel
    #
    cG
    cS
    cT
    crngh
    co
    wcel
    #
    wa
    #
    cS
    crng
    wcel
    #
    cU
    crng
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
    cmgmhm
    co
    wcel
    #
    wa
    @5
    cS
    cU
    crngh
    co
    wcel
    @0
    @4
    @1
    @3
    @0
    cT
    crng
    wcel
    #
    @4
    cT
    cU
    cF
    rnghmrcl
    simprd
    @1
    @3
    @10
    cS
    cT
    cG
    rnghmrcl
    simpld
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
    rnghmghm
    cS
    cT
    cG
    rnghmghm
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
    cmgmhm
    co
    wcel
    cG
    @7
    @11
    cmgmhm
    co
    wcel
    @9
    @1
    cT
    cU
    cF
    @11
    @8
    @11
    eqid
    #
    @8
    eqid
    #
    rnghmmgmhm
    cS
    cT
    cG
    @7
    @11
    @7
    eqid
    #
    @12
    rnghmmgmhm
    @7
    @11
    @8
    cF
    cG
    mgmhmco
    syl2an
    jca
    cS
    cU
    @5
    @7
    @8
    @14
    @13
    isrnghmmul
    sylanbrc
end
