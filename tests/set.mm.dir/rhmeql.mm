include "crh.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cdm.mm"
include "csubrg.mm"
include "cfv.mm"
include "csubg.mm"
include "cmgp.mm"
include "csubmnd.mm"
include "cghm.mm"
include "rhmghm.mm"
include "ghmeql.mm"
include "syl2an.mm"
include "cmhm.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "mhmeql.mm"
include "crg.mm"
include "wb.mm"
include "rhmrcl1.mm"
include "adantr.mm"
include "issubrg3.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem rhmeql
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G


  assert |- ( ( F e. ( S RingHom T ) /\ G e. ( S RingHom T ) ) -> dom ( F i^i G ) e. ( SubRing ` S ) )

  proof
    cF
    cS
    cT
    crh
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cin
    cdm
    #
    cS
    csubrg
    cfv
    wcel
    #
    @4
    cS
    csubg
    cfv
    wcel
    #
    @4
    cS
    cmgp
    cfv
    #
    csubmnd
    cfv
    wcel
    #
    @1
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    cG
    @9
    wcel
    @6
    @2
    cS
    cT
    cF
    rhmghm
    cS
    cT
    cG
    rhmghm
    cS
    cT
    cF
    cG
    ghmeql
    syl2an
    @1
    cF
    @7
    cT
    cmgp
    cfv
    #
    cmhm
    co
    #
    wcel
    cG
    @11
    wcel
    @8
    @2
    cS
    cT
    cF
    @7
    @10
    @7
    eqid
    #
    @10
    eqid
    #
    rhmmhm
    cS
    cT
    cG
    @7
    @10
    @12
    @13
    rhmmhm
    @7
    @10
    cF
    cG
    mhmeql
    syl2an
    @3
    cS
    crg
    wcel
    #
    @5
    @6
    @8
    wa
    wb
    @1
    @14
    @2
    cS
    cT
    cF
    rhmrcl1
    adantr
    cS
    @4
    @7
    @12
    issubrg3
    syl
    mpbir2and
end
