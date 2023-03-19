include "ccvs.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "ccnfld.mm"
include "cress.mm"
include "cdvr.mm"
include "cfv.mm"
include "csubrg.mm"
include "cui.mm"
include "wceq.mm"
include "cclm.mm"
include "simpl.mm"
include "cvsclm.mm"
include "clmsubrg.mm"
include "syl.mm"
include "simpr1.mm"
include "csn.mm"
include "cdif.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cvsunit.mm"
include "clmsca.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "cnflddiv.mm"
include "subrgdv.mm"
include "syl3anc.mm"
include "oveqd.mm"
include "eqtr4d.mm"

theorem cvsdiv
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cW: class W
  assume cvsdiv.f: |- F = ( Scalar ` W )
  assume cvsdiv.k: |- K = ( Base ` F )


  assert |- ( ( W e. CVec /\ ( A e. K /\ B e. K /\ B =/= 0 ) ) -> ( A / B ) = ( A ( /r ` F ) B ) )

  proof
    cW
    ccvs
    wcel
    #
    cA
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cdiv
    co
    #
    cA
    cB
    ccnfld
    cK
    cress
    co
    #
    cdvr
    cfv
    #
    co
    #
    cA
    cB
    cF
    cdvr
    cfv
    #
    co
    @5
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    @1
    cB
    @7
    cui
    cfv
    #
    wcel
    @6
    @9
    wceq
    @5
    cW
    cclm
    wcel
    #
    @11
    @5
    cW
    @0
    @4
    simpl
    #
    cvsclm
    #
    cF
    cK
    cW
    cvsdiv.f
    cvsdiv.k
    clmsubrg
    syl
    @0
    @1
    @2
    @3
    simpr1
    @5
    cB
    cK
    cc0
    csn
    cdif
    #
    @12
    @5
    @2
    @3
    cB
    @16
    wcel
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    cB
    cK
    cc0
    eldifsn
    sylanbrc
    @5
    @16
    cF
    cui
    cfv
    #
    @12
    @5
    @0
    @16
    @17
    wceq
    @14
    cF
    cK
    cW
    cvsdiv.f
    cvsdiv.k
    cvsunit
    syl
    @5
    cF
    @7
    cui
    @5
    @13
    cF
    @7
    wceq
    @15
    cF
    cK
    cW
    cvsdiv.f
    cvsdiv.k
    clmsca
    syl
    #
    fveq2d
    eqtrd
    eleqtrd
    cK
    cdiv
    ccnfld
    @7
    @12
    @8
    cA
    cB
    @7
    eqid
    cnflddiv
    @12
    eqid
    @8
    eqid
    subrgdv
    syl3anc
    @5
    @10
    @8
    cA
    cB
    @5
    cF
    @7
    cdvr
    @18
    fveq2d
    oveqd
    eqtr4d
end
