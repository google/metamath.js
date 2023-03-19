include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "simp3r.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "atlt.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "simp23.mm"
include "3jca.mm"
include "pltle.mm"
include "sylc.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "atbase.mm"
include "syl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "latjcl.mm"
include "pltletr.mm"
include "mpan2d.mm"
include "sylbird.mm"
include "pm2.61dne.mm"

theorem atlelt
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  assume atlelt.b: |- B = ( Base ` K )
  assume atlelt.l: |- .<_ = ( le ` K )
  assume atlelt.s: |- .< = ( lt ` K )
  assume atlelt.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ X e. B ) /\ ( P .<_ X /\ Q .< X ) ) -> P .< X )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    cQ
    cX
    c.lt
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cX
    c.lt
    wbr
    #
    cP
    cQ
    @8
    @9
    cP
    cQ
    wceq
    @6
    @0
    @4
    @5
    @6
    simp3r
    #
    cP
    cQ
    cX
    c.lt
    breq1
    syl5ibrcom
    @8
    cP
    cQ
    wne
    #
    cP
    cP
    cQ
    cK
    cjn
    cfv
    #
    co
    #
    c.lt
    wbr
    #
    @9
    @8
    @0
    @1
    @2
    @14
    @11
    wb
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    cA
    cP
    cQ
    c.lt
    @12
    cK
    atlelt.s
    @12
    eqid
    #
    atlelt.a
    atlt
    syl3anc
    @8
    @14
    @13
    cX
    c.le
    wbr
    #
    @9
    @8
    @5
    cQ
    cX
    c.le
    wbr
    #
    @19
    @0
    @4
    @5
    @6
    simp3l
    @8
    @0
    @2
    @3
    w3a
    @6
    @20
    @8
    @0
    @2
    @3
    @15
    @17
    @0
    @1
    @2
    @3
    @7
    simp23
    #
    3jca
    @10
    chlt
    cA
    cB
    c.lt
    cK
    c.le
    cQ
    cX
    atlelt.l
    atlelt.s
    pltle
    sylc
    @8
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @3
    @5
    @20
    wa
    @19
    wb
    @0
    @4
    @22
    @7
    cK
    hllat
    3ad2ant1
    #
    @8
    @1
    @23
    @16
    cA
    cB
    cP
    cK
    atlelt.b
    atlelt.a
    atbase
    syl
    #
    @8
    @2
    @24
    @17
    cA
    cB
    cQ
    cK
    atlelt.b
    atlelt.a
    atbase
    syl
    #
    @21
    cB
    @12
    cK
    c.le
    cP
    cQ
    cX
    atlelt.b
    atlelt.l
    @18
    latjle12
    syl13anc
    mpbi2and
    @8
    cK
    cpo
    wcel
    #
    @23
    @13
    cB
    wcel
    #
    @3
    @14
    @19
    wa
    @9
    wi
    @0
    @4
    @28
    @7
    cK
    hlpos
    3ad2ant1
    @26
    @8
    @22
    @23
    @24
    @29
    @25
    @26
    @27
    cB
    @12
    cK
    cP
    cQ
    atlelt.b
    @18
    latjcl
    syl3anc
    @21
    cB
    c.lt
    cK
    c.le
    cP
    @13
    cX
    atlelt.b
    atlelt.l
    atlelt.s
    pltletr
    syl13anc
    mpan2d
    sylbird
    pm2.61dne
end
