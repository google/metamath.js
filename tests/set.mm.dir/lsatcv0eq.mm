include "csn.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "cin.mm"
include "lsatnem0.mm"
include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lsatlssel.mm"
include "lcvp.mm"
include "lsatcv0.mm"
include "biantrurd.mm"
include "3bitrd.mm"
include "adantr.mm"
include "lsssn0.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "simprl.mm"
include "simprr.mm"
include "lcvntr.mm"
include "ex.mm"
include "sylbid.mm"
include "necon4ad.mm"
include "csubg.mm"
include "wss.mm"
include "lsssssubg.mm"
include "sseldd.mm"
include "lsmidm.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem lsatcv0eq
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cW: class W
  let c.0: class .0.
  assume lsatcv0eq.o: |- .0. = ( 0g ` W )
  assume lsatcv0eq.p: |- .(+) = ( LSSum ` W )
  assume lsatcv0eq.a: |- A = ( LSAtoms ` W )
  assume lsatcv0eq.c: |- C = ( <oL ` W )
  assume lsatcv0eq.w: |- ( ph -> W e. LVec )
  assume lsatcv0eq.q: |- ( ph -> Q e. A )
  assume lsatcv0eq.r: |- ( ph -> R e. A )


  assert |- ( ph -> ( { .0. } C ( Q .(+) R ) <-> Q = R ) )

  proof
    wph
    c.0
    csn
    #
    cQ
    cR
    c.po
    co
    #
    cC
    wbr
    #
    cQ
    cR
    wceq
    #
    wph
    @2
    cQ
    cR
    wph
    cQ
    cR
    wne
    #
    @0
    cQ
    cC
    wbr
    #
    cQ
    @1
    cC
    wbr
    #
    wa
    #
    @2
    wn
    #
    wph
    @4
    cQ
    cR
    cin
    @0
    wceq
    @6
    @7
    wph
    cA
    cQ
    cR
    cW
    c.0
    lsatcv0eq.o
    lsatcv0eq.a
    lsatcv0eq.w
    lsatcv0eq.q
    lsatcv0eq.r
    lsatnem0
    wph
    cA
    cC
    c.po
    cR
    cW
    clss
    cfv
    #
    cQ
    cW
    c.0
    @9
    eqid
    #
    lsatcv0eq.p
    lsatcv0eq.o
    lsatcv0eq.a
    lsatcv0eq.c
    lsatcv0eq.w
    wph
    cA
    @9
    cQ
    cW
    @10
    lsatcv0eq.a
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    #
    lsatcv0eq.w
    cW
    lveclmod
    syl
    #
    lsatcv0eq.q
    lsatlssel
    #
    lsatcv0eq.r
    lcvp
    wph
    @5
    @6
    wph
    cA
    cC
    cQ
    cW
    c.0
    lsatcv0eq.o
    lsatcv0eq.a
    lsatcv0eq.c
    lsatcv0eq.w
    lsatcv0eq.q
    lsatcv0
    #
    biantrurd
    3bitrd
    wph
    @7
    @8
    wph
    @7
    wa
    cC
    @0
    @9
    cQ
    @1
    cW
    clvec
    @10
    lsatcv0eq.c
    wph
    @11
    @7
    lsatcv0eq.w
    adantr
    wph
    @0
    @9
    wcel
    #
    @7
    wph
    @12
    @16
    @13
    @9
    cW
    c.0
    lsatcv0eq.o
    @10
    lsssn0
    syl
    adantr
    wph
    cQ
    @9
    wcel
    #
    @7
    @14
    adantr
    wph
    @1
    @9
    wcel
    #
    @7
    wph
    @12
    @17
    cR
    @9
    wcel
    @18
    @13
    @14
    wph
    cA
    @9
    cR
    cW
    @10
    lsatcv0eq.a
    @13
    lsatcv0eq.r
    lsatlssel
    c.po
    @9
    cQ
    cR
    cW
    @10
    lsatcv0eq.p
    lsmcl
    syl3anc
    adantr
    wph
    @5
    @6
    simprl
    wph
    @5
    @6
    simprr
    lcvntr
    ex
    sylbid
    necon4ad
    wph
    @0
    cQ
    cQ
    c.po
    co
    #
    cC
    wbr
    @3
    @2
    wph
    @0
    cQ
    @19
    cC
    @15
    wph
    cQ
    cW
    csubg
    cfv
    #
    wcel
    @19
    cQ
    wceq
    wph
    @9
    @20
    cQ
    wph
    @12
    @9
    @20
    wss
    @13
    @9
    cW
    @10
    lsssssubg
    syl
    @14
    sseldd
    c.po
    cQ
    cW
    lsatcv0eq.p
    lsmidm
    syl
    breqtrrd
    @3
    @19
    @1
    @0
    cC
    cQ
    cR
    cQ
    c.po
    oveq2
    breq2d
    syl5ibcom
    impbid
end
