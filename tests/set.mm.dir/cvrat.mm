include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wn.mm"
include "cvratlem.mm"
include "wi.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "adantr.mm"
include "simpr2.mm"
include "atbase.mm"
include "syl.mm"
include "simpr3.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "anbi2d.mm"
include "simpl.mm"
include "simpr1.mm"
include "ex.mm"
include "syl13anc.mm"
include "sylbid.mm"
include "imp.mm"
include "wo.mm"
include "cpo.mm"
include "hlpos.mm"
include "latjcl.mm"
include "eqid.mm"
include "pltnle.mm"
include "wb.mm"
include "latjle12.mm"
include "biimpd.mm"
include "nsyld.mm"
include "ianor.mm"
include "syl6ib.mm"
include "adantrl.mm"
include "mpjaod.mm"

theorem cvrat
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let c.0: class .0.
  let vr: setvar r
  assume cvrat.b: |- B = ( Base ` K )
  assume cvrat.s: |- .< = ( lt ` K )
  assume cvrat.j: |- .\/ = ( join ` K )
  assume cvrat.z: |- .0. = ( 0. ` K )
  assume cvrat.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( X e. B /\ P e. A /\ Q e. A ) ) -> ( ( X =/= .0. /\ X .< ( P .\/ Q ) ) -> X e. A ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
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
    w3a
    #
    wa
    #
    cX
    c.0
    wne
    #
    cX
    cP
    cQ
    c.or
    co
    #
    c.lt
    wbr
    #
    wa
    #
    cX
    cA
    wcel
    #
    @5
    @9
    wa
    cP
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @10
    cQ
    cX
    @11
    wbr
    #
    wn
    #
    cA
    cB
    cP
    cQ
    c.lt
    c.or
    cK
    cX
    c.0
    cvrat.b
    cvrat.s
    cvrat.j
    cvrat.z
    cvrat.a
    cvratlem
    @5
    @9
    @15
    @10
    wi
    #
    @5
    @9
    @6
    cX
    cQ
    cP
    c.or
    co
    #
    c.lt
    wbr
    #
    wa
    #
    @16
    @5
    @8
    @18
    @6
    @5
    @7
    @17
    cX
    c.lt
    @5
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
    @7
    @17
    wceq
    @0
    @20
    @4
    cK
    hllat
    adantr
    #
    @5
    @2
    @21
    @0
    @1
    @2
    @3
    simpr2
    #
    cA
    cB
    cP
    cK
    cvrat.b
    cvrat.a
    atbase
    syl
    #
    @5
    @3
    @22
    @0
    @1
    @2
    @3
    simpr3
    #
    cA
    cB
    cQ
    cK
    cvrat.b
    cvrat.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cP
    cQ
    cvrat.b
    cvrat.j
    latjcom
    syl3anc
    breq2d
    anbi2d
    @5
    @0
    @1
    @3
    @2
    @19
    @16
    wi
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    #
    @26
    @24
    @0
    @1
    @3
    @2
    w3a
    wa
    @19
    @16
    cA
    cB
    cQ
    cP
    c.lt
    c.or
    cK
    cX
    c.0
    cvrat.b
    cvrat.s
    cvrat.j
    cvrat.z
    cvrat.a
    cvratlem
    ex
    syl13anc
    sylbid
    imp
    @5
    @8
    @13
    @15
    wo
    #
    @6
    @5
    @8
    @29
    @5
    @8
    @12
    @14
    wa
    #
    wn
    @29
    @5
    @8
    @7
    cX
    @11
    wbr
    #
    @30
    @5
    cK
    cpo
    wcel
    #
    @1
    @7
    cB
    wcel
    #
    @8
    @31
    wn
    #
    wi
    @0
    @32
    @4
    cK
    hlpos
    adantr
    @28
    @5
    @20
    @21
    @22
    @33
    @23
    @25
    @27
    cB
    c.or
    cK
    cP
    cQ
    cvrat.b
    cvrat.j
    latjcl
    syl3anc
    @32
    @1
    @33
    w3a
    @8
    @34
    cB
    c.lt
    cK
    @11
    cX
    @7
    cvrat.b
    @11
    eqid
    #
    cvrat.s
    pltnle
    ex
    syl3anc
    @5
    @30
    @31
    @5
    @20
    @21
    @22
    @1
    @30
    @31
    wb
    @23
    @25
    @27
    @28
    cB
    c.or
    cK
    @11
    cP
    cQ
    cX
    cvrat.b
    @35
    cvrat.j
    latjle12
    syl13anc
    biimpd
    nsyld
    @12
    @14
    ianor
    syl6ib
    imp
    adantrl
    mpjaod
    ex
end
