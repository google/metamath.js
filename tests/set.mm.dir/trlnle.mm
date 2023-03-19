include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cp0.mm"
include "cal.mm"
include "simpl1l.mm"
include "hlatl.mm"
include "syl.mm"
include "simpl3l.mm"
include "eqid.mm"
include "atnle0.mm"
include "syl2anc.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpl2.mm"
include "simpr.mm"
include "trl0.mm"
include "syl112anc.mm"
include "breq2d.mm"
include "mtbird.mm"
include "wne.mm"
include "trlne.mm"
include "adantr.mm"
include "wb.mm"
include "trlat.mm"
include "atncmp.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem trlnle
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trlne.l: |- .<_ = ( le ` K )
  assume trlne.a: |- A = ( Atoms ` K )
  assume trlne.h: |- H = ( LHyp ` K )
  assume trlne.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlne.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> -. P .<_ ( R ` F ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cF
    cR
    cfv
    #
    c.le
    wbr
    #
    wn
    #
    cP
    cF
    cfv
    #
    cP
    @7
    @11
    cP
    wceq
    #
    wa
    #
    @9
    cP
    cK
    cp0
    cfv
    #
    c.le
    wbr
    #
    @13
    cK
    cal
    wcel
    #
    @4
    @15
    wn
    @13
    @0
    @16
    @0
    @1
    @3
    @6
    @12
    simpl1l
    cK
    hlatl
    #
    syl
    @4
    @5
    @2
    @3
    @12
    simpl3l
    cA
    cP
    cK
    c.le
    @14
    trlne.l
    @14
    eqid
    #
    trlne.a
    atnle0
    syl2anc
    @13
    @8
    @14
    cP
    c.le
    @13
    @2
    @6
    @3
    @12
    @8
    @14
    wceq
    @2
    @3
    @6
    @12
    simpl1
    @2
    @3
    @6
    @12
    simpl3
    @2
    @3
    @6
    @12
    simpl2
    @7
    @12
    simpr
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    @14
    trlne.l
    @18
    trlne.a
    trlne.h
    trlne.t
    trlne.r
    trl0
    syl112anc
    breq2d
    mtbird
    @7
    @11
    cP
    wne
    #
    wa
    #
    @10
    cP
    @8
    wne
    #
    @7
    @21
    @19
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    trlne.l
    trlne.a
    trlne.h
    trlne.t
    trlne.r
    trlne
    adantr
    @20
    @16
    @4
    @8
    cA
    wcel
    #
    @10
    @21
    wb
    @20
    @0
    @16
    @0
    @1
    @3
    @6
    @19
    simpl1l
    @17
    syl
    @4
    @5
    @2
    @3
    @19
    simpl3l
    @20
    @2
    @6
    @3
    @19
    @22
    @2
    @3
    @6
    @19
    simpl1
    @2
    @3
    @6
    @19
    simpl3
    @2
    @3
    @6
    @19
    simpl2
    @7
    @19
    simpr
    cA
    cP
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    trlne.l
    trlne.a
    trlne.h
    trlne.t
    trlne.r
    trlat
    syl112anc
    cA
    cP
    @8
    cK
    c.le
    trlne.l
    trlne.a
    atncmp
    syl3anc
    mpbird
    pm2.61dane
end
