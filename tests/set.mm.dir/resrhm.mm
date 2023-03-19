include "crh.mm"
include "co.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "crg.mm"
include "cres.mm"
include "cghm.mm"
include "cmgp.mm"
include "cmhm.mm"
include "rhmrcl2.mm"
include "subrgring.mm"
include "anim12ci.mm"
include "csubg.mm"
include "rhmghm.mm"
include "subrgsubg.mm"
include "resghm.mm"
include "syl2an.mm"
include "cress.mm"
include "csubmnd.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "subrgsubm.mm"
include "resmhm.mm"
include "wceq.mm"
include "rhmrcl1.mm"
include "mgpress.mm"
include "sylan.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "jca.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem resrhm
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cX: class X
  assume resrhm.u: |- U = ( S |`s X )


  assert |- ( ( F e. ( S RingHom T ) /\ X e. ( SubRing ` S ) ) -> ( F |` X ) e. ( U RingHom T ) )

  proof
    cF
    cS
    cT
    crh
    co
    wcel
    #
    cX
    cS
    csubrg
    cfv
    #
    wcel
    #
    wa
    #
    cU
    crg
    wcel
    #
    cT
    crg
    wcel
    #
    wa
    cF
    cX
    cres
    #
    cU
    cT
    cghm
    co
    wcel
    #
    @6
    cU
    cmgp
    cfv
    #
    cT
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    #
    wa
    @6
    cU
    cT
    crh
    co
    wcel
    @0
    @5
    @2
    @4
    cS
    cT
    cF
    rhmrcl2
    cX
    cS
    cU
    resrhm.u
    subrgring
    anim12ci
    @3
    @7
    @11
    @0
    cF
    cS
    cT
    cghm
    co
    wcel
    cX
    cS
    csubg
    cfv
    wcel
    @7
    @2
    cS
    cT
    cF
    rhmghm
    cX
    cS
    subrgsubg
    cS
    cT
    cU
    cF
    cX
    resrhm.u
    resghm
    syl2an
    @3
    @6
    cS
    cmgp
    cfv
    #
    cX
    cress
    co
    #
    @9
    cmhm
    co
    #
    @10
    @0
    cF
    @12
    @9
    cmhm
    co
    wcel
    cX
    @12
    csubmnd
    cfv
    wcel
    @6
    @14
    wcel
    @2
    cS
    cT
    cF
    @12
    @9
    @12
    eqid
    #
    @9
    eqid
    #
    rhmmhm
    cX
    cS
    @12
    @15
    subrgsubm
    @12
    @9
    @13
    cF
    cX
    @13
    eqid
    resmhm
    syl2an
    @3
    @13
    @8
    @9
    cmhm
    @0
    cS
    crg
    wcel
    @2
    @13
    @8
    wceq
    cS
    cT
    cF
    rhmrcl1
    cX
    cS
    cU
    @12
    crg
    @1
    resrhm.u
    @15
    mgpress
    sylan
    oveq1d
    eleqtrd
    jca
    cU
    cT
    @6
    @8
    @9
    @8
    eqid
    @16
    isrhm
    sylanbrc
end
