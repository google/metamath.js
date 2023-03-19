include "cfn.mm"
include "wcel.mm"
include "cevpm.mm"
include "cfv.mm"
include "cdif.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "cneg.mm"
include "wo.mm"
include "eldif.mm"
include "simpr.mm"
include "a1d.mm"
include "ancrd.mm"
include "wb.mm"
include "psgnevpmb.mm"
include "adantr.mm"
include "sylibrd.mm"
include "con3d.mm"
include "impr.mm"
include "sylan2b.mm"
include "cpr.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cress.mm"
include "co.mm"
include "cghm.mm"
include "wf.mm"
include "eqid.mm"
include "psgnghm2.mm"
include "cnmsgnbas.mm"
include "ghmf.mm"
include "syl.mm"
include "eldifi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "fvex.mm"
include "elpr.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"

theorem psgnodpm
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cN: class N
  let vd: setvar d
  assume evpmss.s: |- S = ( SymGrp ` D )
  assume evpmss.p: |- P = ( Base ` S )
  assume psgnevpmb.n: |- N = ( pmSgn ` D )


  assert |- ( ( D e. Fin /\ F e. ( P \ ( pmEven ` D ) ) ) -> ( N ` F ) = -u 1 )

  proof
    cD
    cfn
    wcel
    #
    cF
    cP
    cD
    cevpm
    cfv
    #
    cdif
    wcel
    #
    wa
    #
    cF
    cN
    cfv
    #
    c1
    wceq
    #
    wn
    #
    @5
    @4
    c1
    cneg
    #
    wceq
    #
    wo
    #
    @8
    @2
    @0
    cF
    cP
    wcel
    #
    cF
    @1
    wcel
    #
    wn
    #
    wa
    @6
    cF
    cP
    @1
    eldif
    @0
    @10
    @12
    @6
    @0
    @10
    wa
    #
    @5
    @11
    @13
    @5
    @10
    @5
    wa
    #
    @11
    @13
    @5
    @10
    @13
    @10
    @5
    @0
    @10
    simpr
    a1d
    ancrd
    @0
    @11
    @14
    wb
    @10
    cD
    cP
    cS
    cF
    cN
    evpmss.s
    evpmss.p
    psgnevpmb.n
    psgnevpmb
    adantr
    sylibrd
    con3d
    impr
    sylan2b
    @3
    @4
    c1
    @7
    cpr
    #
    wcel
    @9
    @3
    cP
    @15
    cF
    cN
    @3
    cN
    cS
    ccnfld
    cmgp
    cfv
    @15
    cress
    co
    #
    cghm
    co
    wcel
    #
    cP
    @15
    cN
    wf
    @0
    @17
    @2
    cD
    cS
    @16
    cN
    evpmss.s
    psgnevpmb.n
    @16
    eqid
    #
    psgnghm2
    adantr
    cS
    @16
    cN
    cP
    @15
    evpmss.p
    @16
    @18
    cnmsgnbas
    ghmf
    syl
    @2
    @10
    @0
    cF
    cP
    @1
    eldifi
    adantl
    ffvelrnd
    @4
    c1
    @7
    cF
    cN
    fvex
    elpr
    sylib
    @5
    @8
    orel1
    sylc
end
