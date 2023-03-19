include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "clinc.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cpw.mm"
include "wceq.mm"
include "simpl1.mm"
include "simprl.mm"
include "cvv.mm"
include "ssexg.mm"
include "ancoms.mm"
include "wi.mm"
include "eqid.mm"
include "lssss.mm"
include "sstr.mm"
include "elpwg.mm"
include "syl5ibrcom.mm"
include "expcom.mm"
include "syl.mm"
include "imp.mm"
include "mpd.mm"
include "3adant1.mm"
include "adantr.mm"
include "lincval.mm"
include "syl3anc.mm"
include "gsumlsscl.mm"
include "eqeltrd.mm"
include "ex.mm"

theorem lincellss
  let cS: class S
  let cF: class F
  let cM: class M
  let cV: class V
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. LMod /\ S e. ( LSubSp ` M ) /\ V C_ S ) -> ( ( F e. ( ( Base ` ( Scalar ` M ) ) ^m V ) /\ F finSupp ( 0g ` ( Scalar ` M ) ) ) -> ( F ( linC ` M ) V ) e. S ) )

  proof
    cM
    clmod
    wcel
    #
    cS
    cM
    clss
    cfv
    #
    wcel
    #
    cV
    cS
    wss
    #
    w3a
    #
    cF
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cmap
    co
    wcel
    #
    cF
    @5
    c0g
    cfv
    cfsupp
    wbr
    #
    wa
    #
    cF
    cV
    cM
    clinc
    cfv
    co
    #
    cS
    wcel
    @4
    @9
    wa
    #
    @10
    cM
    vv
    cV
    vv
    cv
    #
    cF
    cfv
    @12
    cM
    cvsca
    cfv
    co
    cmpt
    cgsu
    co
    #
    cS
    @11
    @0
    @7
    cV
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @10
    @13
    wceq
    @0
    @2
    @3
    @9
    simpl1
    @4
    @7
    @8
    simprl
    @4
    @15
    @9
    @2
    @3
    @15
    @0
    @2
    @3
    wa
    cV
    cvv
    wcel
    #
    @15
    @3
    @2
    @16
    cV
    cS
    @1
    ssexg
    ancoms
    @2
    @3
    @16
    @15
    wi
    #
    @2
    cS
    @14
    wss
    #
    @3
    @17
    wi
    @1
    cS
    @14
    cM
    @14
    eqid
    @1
    eqid
    #
    lssss
    @3
    @18
    @17
    @3
    @18
    wa
    @15
    @16
    cV
    @14
    wss
    cV
    cS
    @14
    sstr
    cV
    @14
    cvv
    elpwg
    syl5ibrcom
    expcom
    syl
    imp
    mpd
    3adant1
    adantr
    vv
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @4
    @9
    @13
    cS
    wcel
    vv
    @6
    @5
    @1
    cF
    cM
    cV
    cS
    @19
    @5
    eqid
    @6
    eqid
    gsumlsscl
    imp
    eqeltrd
    ex
end
