include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wpss.mm"
include "w3a.mm"
include "cv.mm"
include "wn.mm"
include "cfv.mm"
include "wex.mm"
include "pssnel.mm"
include "3ad2ant3.mm"
include "wss.mm"
include "simpl2.mm"
include "lbsss.mm"
include "syl.mm"
include "simprl.mm"
include "sseldd.mm"
include "csn.mm"
include "cdif.mm"
include "simpl1l.mm"
include "ssdifssd.mm"
include "simpl3.mm"
include "pssssd.mm"
include "sseld.mm"
include "weq.mm"
include "simprr.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "jcad.mm"
include "eldifsn.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "lspss.mm"
include "syl3anc.mm"
include "simpl1r.mm"
include "lbsind2.mm"
include "syl211anc.mm"
include "ssneldd.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "necomd.mm"
include "exlimddv.mm"

theorem lbspss
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cF: class F
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume lbsind2.j: |- J = ( LBasis ` W )
  assume lbsind2.n: |- N = ( LSpan ` W )
  assume lbsind2.f: |- F = ( Scalar ` W )
  assume lbsind2.o: |- .1. = ( 1r ` F )
  assume lbsind2.z: |- .0. = ( 0g ` F )
  assume lbspss.v: |- V = ( Base ` W )


  assert |- ( ( ( W e. LMod /\ .1. =/= .0. ) /\ B e. J /\ C C. B ) -> ( N ` C ) =/= V )

  proof
    cW
    clmod
    wcel
    #
    c.1
    c.0
    wne
    #
    wa
    #
    cB
    cJ
    wcel
    #
    cC
    cB
    wpss
    #
    w3a
    #
    vx
    cv
    #
    cB
    wcel
    #
    @6
    cC
    wcel
    #
    wn
    #
    wa
    #
    cC
    cN
    cfv
    #
    cV
    wne
    vx
    @4
    @2
    @10
    vx
    wex
    @3
    vx
    cC
    cB
    pssnel
    3ad2ant3
    @5
    @10
    wa
    #
    cV
    @11
    @12
    @6
    cV
    wcel
    @6
    @11
    wcel
    wn
    cV
    @11
    wne
    @12
    cB
    cV
    @6
    @12
    @3
    cB
    cV
    wss
    @2
    @3
    @4
    @10
    simpl2
    #
    cB
    cJ
    cV
    cW
    lbspss.v
    lbsind2.j
    lbsss
    syl
    #
    @5
    @7
    @9
    simprl
    #
    sseldd
    @12
    @11
    cB
    @6
    csn
    #
    cdif
    #
    cN
    cfv
    #
    @6
    @12
    @0
    @17
    cV
    wss
    cC
    @17
    wss
    @11
    @18
    wss
    @0
    @1
    @3
    @4
    @10
    simpl1l
    #
    @12
    cB
    cV
    @16
    @14
    ssdifssd
    @12
    vy
    cC
    @17
    @12
    vy
    cv
    #
    cC
    wcel
    #
    @20
    cB
    wcel
    #
    @20
    @6
    wne
    #
    wa
    @20
    @17
    wcel
    @12
    @21
    @22
    @23
    @12
    cC
    cB
    @20
    @12
    cC
    cB
    @2
    @3
    @4
    @10
    simpl3
    pssssd
    sseld
    @12
    @21
    @20
    @6
    @12
    @21
    wn
    vy
    vx
    weq
    #
    @9
    @5
    @7
    @9
    simprr
    @24
    @21
    @8
    @20
    @6
    cC
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    jcad
    @20
    cB
    @6
    eldifsn
    syl6ibr
    ssrdv
    cC
    @17
    cN
    cV
    cW
    lbspss.v
    lbsind2.n
    lspss
    syl3anc
    @12
    @0
    @1
    @3
    @7
    @6
    @18
    wcel
    wn
    @19
    @0
    @1
    @3
    @4
    @10
    simpl1r
    @13
    @15
    cB
    c.1
    @6
    cF
    cJ
    cN
    cW
    c.0
    lbsind2.j
    lbsind2.n
    lbsind2.f
    lbsind2.o
    lbsind2.z
    lbsind2
    syl211anc
    ssneldd
    @6
    cV
    @11
    nelne1
    syl2anc
    necomd
    exlimddv
end
