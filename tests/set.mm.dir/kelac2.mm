include "cid.mm"
include "cres.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cpr.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ccmp.mm"
include "ctop.mm"
include "kelac2lem.mm"
include "cmptop.mm"
include "3syl.mm"
include "ccld.mm"
include "cdif.mm"
include "cun.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "uniprg.mm"
include "sylancl.mm"
include "difeq1d.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "wn.mm"
include "pwuninel.mm"
include "a1i.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "disj3.mm"
include "sylib.mm"
include "3eqtr4a.mm"
include "wss.mm"
include "prex.mm"
include "bastg.mm"
include "mp1i.mm"
include "prid2.mm"
include "sseldd.mm"
include "eqeltrd.mm"
include "wb.mm"
include "prid1g.mm"
include "elssuni.mm"
include "unitg.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "wf1o.mm"
include "f1oi.mm"
include "uniexg.mm"
include "pwexg.mm"
include "snidg.mm"
include "4syl.mm"
include "syl6eleqr.mm"
include "kelac1.mm"

theorem kelac2
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cI: class I
  let cV: class V
  assume kelac2.s: |- ( ( ph /\ x e. I ) -> S e. V )
  assume kelac2.z: |- ( ( ph /\ x e. I ) -> S =/= (/) )
  assume kelac2.k: |- ( ph -> ( Xt_ ` ( x e. I |-> ( topGen ` { S , { ~P U. S } } ) ) ) e. Comp )

  disjoint ph x
  disjoint I x
  assert |- ( ph -> X_ x e. I S =/= (/) )

  proof
    wph
    vx
    cid
    cS
    cres
    #
    cS
    cS
    cS
    cuni
    #
    cpw
    #
    cI
    cS
    @2
    csn
    #
    cpr
    #
    ctg
    cfv
    #
    kelac2.z
    wph
    vx
    cv
    cI
    wcel
    wa
    #
    cS
    cV
    wcel
    #
    @5
    ccmp
    wcel
    @5
    ctop
    wcel
    #
    kelac2.s
    cS
    cV
    kelac2lem
    @5
    cmptop
    3syl
    #
    @6
    cS
    @5
    ccld
    cfv
    wcel
    #
    @4
    cuni
    #
    cS
    cdif
    #
    @5
    wcel
    #
    @6
    @12
    @3
    @5
    @6
    cS
    @3
    cun
    #
    cS
    cdif
    #
    @3
    cS
    cdif
    #
    @12
    @3
    @15
    @3
    cS
    cun
    #
    cS
    cdif
    @16
    @14
    @17
    cS
    cS
    @3
    uncom
    difeq1i
    @3
    cS
    difun2
    eqtri
    @6
    @11
    @14
    cS
    @6
    @7
    @3
    cvv
    wcel
    @11
    @14
    wceq
    kelac2.s
    @2
    snex
    #
    cS
    @3
    cV
    cvv
    uniprg
    sylancl
    difeq1d
    @6
    @3
    cS
    cin
    #
    c0
    wceq
    @3
    @16
    wceq
    @6
    @19
    cS
    @3
    cin
    #
    c0
    @3
    cS
    incom
    @6
    @2
    cS
    wcel
    wn
    #
    @20
    c0
    wceq
    @21
    @6
    cS
    pwuninel
    a1i
    cS
    @2
    disjsn
    sylibr
    syl5eq
    @3
    cS
    disj3
    sylib
    3eqtr4a
    @6
    @4
    @5
    @3
    @4
    cvv
    wcel
    #
    @4
    @5
    wss
    @6
    cS
    @3
    prex
    #
    @4
    cvv
    bastg
    mp1i
    @3
    @4
    wcel
    #
    @6
    cS
    @3
    @18
    prid2
    #
    a1i
    sseldd
    eqeltrd
    @6
    @8
    cS
    @11
    wss
    #
    @10
    @13
    wb
    @9
    @6
    @7
    cS
    @4
    wcel
    @26
    kelac2.s
    cS
    @3
    cV
    prid1g
    cS
    @4
    elssuni
    3syl
    cS
    @5
    @11
    @5
    cuni
    #
    @11
    @22
    @27
    @11
    wceq
    @23
    @4
    cvv
    unitg
    ax-mp
    #
    eqcomi
    iscld2
    syl2anc
    mpbird
    cS
    cS
    @0
    wf1o
    @6
    cS
    f1oi
    a1i
    @6
    @2
    @11
    @27
    @6
    @3
    @11
    @2
    @24
    @3
    @11
    wss
    @6
    @25
    @3
    @4
    elssuni
    mp1i
    @6
    @7
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @2
    @3
    wcel
    kelac2.s
    cS
    cV
    uniexg
    @1
    cvv
    pwexg
    @2
    cvv
    snidg
    4syl
    sseldd
    @28
    syl6eleqr
    kelac2.k
    kelac1
end
