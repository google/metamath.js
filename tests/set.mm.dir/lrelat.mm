include "cv.mm"
include "wss.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "co.mm"
include "wpss.mm"
include "lpssat.mm"
include "wcel.mm"
include "ancom.mm"
include "csubg.mm"
include "cfv.mm"
include "clmod.mm"
include "adantr.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "simpr.mm"
include "lsatlssel.mm"
include "lssnle.mm"
include "pssssd.mm"
include "biantrurd.mm"
include "wb.mm"
include "lsmlub.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem lrelat
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vq: setvar q
  assume lrelat.s: |- S = ( LSubSp ` W )
  assume lrelat.p: |- .(+) = ( LSSum ` W )
  assume lrelat.a: |- A = ( LSAtoms ` W )
  assume lrelat.w: |- ( ph -> W e. LMod )
  assume lrelat.t: |- ( ph -> T e. S )
  assume lrelat.u: |- ( ph -> U e. S )
  assume lrelat.l: |- ( ph -> T C. U )

  disjoint A q
  disjoint S q
  disjoint T q
  disjoint U q
  disjoint W q
  disjoint ph q
  assert |- ( ph -> E. q e. A ( T C. ( T .(+) q ) /\ ( T .(+) q ) C_ U ) )

  proof
    wph
    vq
    cv
    #
    cU
    wss
    #
    @0
    cT
    wss
    wn
    #
    wa
    #
    vq
    cA
    wrex
    cT
    cT
    @0
    c.po
    co
    #
    wpss
    #
    @4
    cU
    wss
    #
    wa
    #
    vq
    cA
    wrex
    wph
    cA
    cS
    cT
    cU
    cW
    vq
    lrelat.s
    lrelat.a
    lrelat.w
    lrelat.t
    lrelat.u
    lrelat.l
    lpssat
    wph
    @3
    @7
    vq
    cA
    @3
    @2
    @1
    wa
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @7
    @1
    @2
    ancom
    @9
    @2
    @5
    @1
    @6
    @9
    c.po
    cT
    @0
    cW
    lrelat.p
    @9
    cS
    cW
    csubg
    cfv
    #
    cT
    @9
    cW
    clmod
    wcel
    #
    cS
    @10
    wss
    wph
    @11
    @8
    lrelat.w
    adantr
    #
    cS
    cW
    lrelat.s
    lsssssubg
    syl
    #
    wph
    cT
    cS
    wcel
    @8
    lrelat.t
    adantr
    sseldd
    #
    @9
    cS
    @10
    @0
    @13
    @9
    cA
    cS
    @0
    cW
    lrelat.s
    lrelat.a
    @12
    wph
    @8
    simpr
    lsatlssel
    sseldd
    #
    lssnle
    @9
    @1
    cT
    cU
    wss
    #
    @1
    wa
    #
    @6
    @9
    @16
    @1
    wph
    @16
    @8
    wph
    cT
    cU
    lrelat.l
    pssssd
    adantr
    biantrurd
    @9
    cT
    @10
    wcel
    @0
    @10
    wcel
    cU
    @10
    wcel
    @17
    @6
    wb
    @14
    @15
    @9
    cS
    @10
    cU
    @13
    wph
    cU
    cS
    wcel
    @8
    lrelat.u
    adantr
    sseldd
    c.po
    cT
    @0
    cU
    cW
    lrelat.p
    lsmlub
    syl3anc
    bitrd
    anbi12d
    syl5bb
    rexbidva
    mpbid
end
