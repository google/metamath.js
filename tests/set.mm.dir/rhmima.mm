include "crh.mm"
include "co.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "wa.mm"
include "cima.mm"
include "csubg.mm"
include "cmgp.mm"
include "csubmnd.mm"
include "cghm.mm"
include "rhmghm.mm"
include "subrgsubg.mm"
include "ghmima.mm"
include "syl2an.mm"
include "cmhm.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "subrgsubm.mm"
include "mhmima.mm"
include "crg.mm"
include "wb.mm"
include "rhmrcl2.mm"
include "adantr.mm"
include "issubrg3.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem rhmima
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X


  assert |- ( ( F e. ( M RingHom N ) /\ X e. ( SubRing ` M ) ) -> ( F " X ) e. ( SubRing ` N ) )

  proof
    cF
    cM
    cN
    crh
    co
    wcel
    #
    cX
    cM
    csubrg
    cfv
    wcel
    #
    wa
    #
    cF
    cX
    cima
    #
    cN
    csubrg
    cfv
    wcel
    #
    @3
    cN
    csubg
    cfv
    wcel
    #
    @3
    cN
    cmgp
    cfv
    #
    csubmnd
    cfv
    wcel
    #
    @0
    cF
    cM
    cN
    cghm
    co
    wcel
    cX
    cM
    csubg
    cfv
    wcel
    @5
    @1
    cM
    cN
    cF
    rhmghm
    cX
    cM
    subrgsubg
    cM
    cN
    cX
    cF
    ghmima
    syl2an
    @0
    cF
    cM
    cmgp
    cfv
    #
    @6
    cmhm
    co
    wcel
    cX
    @8
    csubmnd
    cfv
    wcel
    @7
    @1
    cM
    cN
    cF
    @8
    @6
    @8
    eqid
    #
    @6
    eqid
    #
    rhmmhm
    cX
    cM
    @8
    @9
    subrgsubm
    cF
    @8
    @6
    cX
    mhmima
    syl2an
    @2
    cN
    crg
    wcel
    #
    @4
    @5
    @7
    wa
    wb
    @0
    @11
    @1
    cM
    cN
    cF
    rhmrcl2
    adantr
    cN
    @3
    @6
    @10
    issubrg3
    syl
    mpbir2and
end
