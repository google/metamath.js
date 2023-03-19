include "cfn.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "wceq.mm"
include "w3a.mm"
include "cevpm.mm"
include "simp2.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "wi.mm"
include "psgnevpm.mm"
include "ex.mm"
include "adantr.mm"
include "neg1rr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "neg1lt0.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "lttri.mm"
include "mp2an.mm"
include "gtneii.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "syl6.mm"
include "necon2bd.mm"
include "3impia.mm"
include "eldifd.mm"

theorem psgnodpmr
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cN: class N
  let vd: setvar d
  assume evpmss.s: |- S = ( SymGrp ` D )
  assume evpmss.p: |- P = ( Base ` S )
  assume psgnevpmb.n: |- N = ( pmSgn ` D )


  assert |- ( ( D e. Fin /\ F e. P /\ ( N ` F ) = -u 1 ) -> F e. ( P \ ( pmEven ` D ) ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cP
    wcel
    #
    cF
    cN
    cfv
    #
    c1
    cneg
    #
    wceq
    #
    w3a
    cF
    cP
    cD
    cevpm
    cfv
    #
    @0
    @1
    @4
    simp2
    @0
    @1
    @4
    cF
    @5
    wcel
    #
    wn
    @0
    @1
    wa
    #
    @6
    @2
    @3
    @7
    @6
    @2
    c1
    wceq
    #
    @2
    @3
    wne
    #
    @0
    @6
    @8
    wi
    @1
    @0
    @6
    @8
    cD
    cP
    cS
    cF
    cN
    evpmss.s
    evpmss.p
    psgnevpmb.n
    psgnevpm
    ex
    adantr
    @8
    @9
    c1
    @3
    wne
    @3
    c1
    neg1rr
    @3
    cc0
    clt
    wbr
    cc0
    c1
    clt
    wbr
    @3
    c1
    clt
    wbr
    neg1lt0
    0lt1
    @3
    cc0
    c1
    neg1rr
    0re
    1re
    lttri
    mp2an
    gtneii
    @2
    c1
    @3
    neeq1
    mpbiri
    syl6
    necon2bd
    3impia
    eldifd
end
