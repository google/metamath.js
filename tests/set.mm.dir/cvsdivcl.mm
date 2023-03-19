include "ccvs.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cdvr.mm"
include "cfv.mm"
include "cvsdiv.mm"
include "crg.mm"
include "cui.mm"
include "clvec.mm"
include "cdr.mm"
include "simpl.mm"
include "cvslvec.mm"
include "lvecdrng.mm"
include "drngring.mm"
include "3syl.mm"
include "simpr1.mm"
include "csn.mm"
include "cdif.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "wceq.mm"
include "cvsunit.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "dvrcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem cvsdivcl
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let cW: class W
  assume cvsdiv.f: |- F = ( Scalar ` W )
  assume cvsdiv.k: |- K = ( Base ` F )


  assert |- ( ( W e. CVec /\ ( A e. K /\ B e. K /\ B =/= 0 ) ) -> ( A / B ) e. K )

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
    cA
    cB
    cF
    cdvr
    cfv
    #
    co
    #
    cK
    cA
    cB
    cF
    cK
    cW
    cvsdiv.f
    cvsdiv.k
    cvsdiv
    @5
    cF
    crg
    wcel
    #
    @1
    cB
    cF
    cui
    cfv
    #
    wcel
    @7
    cK
    wcel
    @5
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    @8
    @5
    cW
    @0
    @4
    simpl
    cvslvec
    cF
    cW
    cvsdiv.f
    lvecdrng
    cF
    drngring
    3syl
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
    @9
    @5
    @2
    @3
    cB
    @10
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
    @0
    @10
    @9
    wceq
    @4
    cF
    cK
    cW
    cvsdiv.f
    cvsdiv.k
    cvsunit
    adantr
    eleqtrd
    cK
    @6
    cF
    @9
    cA
    cB
    cvsdiv.k
    @9
    eqid
    @6
    eqid
    dvrcl
    syl3anc
    eqeltrd
end
