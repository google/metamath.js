include "cal.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "snssi.mm"
include "adantl.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "atllat.mm"
include "eqid.mm"
include "atbase.mm"
include "latjidm.mm"
include "syl2an.mm"
include "adantr.mm"
include "breq2d.mm"
include "wb.mm"
include "atcmp.mm"
include "3com23.mm"
include "3expa.mm"
include "biimpd.mm"
include "sylbid.mm"
include "adantld.mm"
include "velsn.mm"
include "anbi12i.mm"
include "anbi1i.mm"
include "oveq12.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "3imtr4g.mm"
include "exp4b.mm"
include "com23.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "jca.mm"
include "ex.mm"
include "ispsubsp.mm"
include "sylibrd.mm"
include "imp.mm"

theorem snatpsubN
  let cA: class A
  let cP: class P
  let cS: class S
  let cK: class K
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume snpsub.a: |- A = ( Atoms ` K )
  assume snpsub.s: |- S = ( PSubSp ` K )


  assert |- ( ( K e. AtLat /\ P e. A ) -> { P } e. S )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    csn
    #
    cS
    wcel
    #
    @0
    @1
    @2
    cA
    wss
    #
    vr
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @5
    @2
    wcel
    #
    wi
    #
    vr
    cA
    wral
    #
    vq
    @2
    wral
    vp
    @2
    wral
    #
    wa
    #
    @3
    @0
    @1
    @16
    @0
    @1
    wa
    #
    @4
    @15
    @1
    @4
    @0
    cP
    cA
    snssi
    adantl
    @17
    @14
    vp
    vq
    @2
    @2
    @17
    @6
    @2
    wcel
    #
    @7
    @2
    wcel
    #
    wa
    #
    @13
    vr
    cA
    @17
    @5
    cA
    wcel
    #
    @20
    @13
    @17
    @21
    @20
    @11
    @12
    @17
    @21
    wa
    #
    @6
    cP
    wceq
    #
    @7
    cP
    wceq
    #
    wa
    #
    @5
    cP
    cP
    @8
    co
    #
    @10
    wbr
    #
    wa
    #
    @5
    cP
    wceq
    #
    @20
    @11
    wa
    #
    @12
    @22
    @27
    @29
    @25
    @22
    @27
    @5
    cP
    @10
    wbr
    #
    @29
    @22
    @26
    cP
    @5
    @10
    @17
    @26
    cP
    wceq
    #
    @21
    @0
    cK
    clat
    wcel
    cP
    cK
    cbs
    cfv
    #
    wcel
    @32
    @1
    cK
    atllat
    cA
    @33
    cP
    cK
    @33
    eqid
    #
    snpsub.a
    atbase
    @33
    @8
    cK
    cP
    @34
    @8
    eqid
    #
    latjidm
    syl2an
    adantr
    breq2d
    @22
    @31
    @29
    @0
    @1
    @21
    @31
    @29
    wb
    #
    @0
    @21
    @1
    @36
    cA
    @5
    cP
    cK
    @10
    @10
    eqid
    #
    snpsub.a
    atcmp
    3com23
    3expa
    biimpd
    sylbid
    adantld
    @30
    @25
    @11
    wa
    @28
    @20
    @25
    @11
    @18
    @23
    @19
    @24
    vp
    cP
    velsn
    vq
    cP
    velsn
    anbi12i
    anbi1i
    @25
    @11
    @27
    @25
    @9
    @26
    @5
    @10
    @6
    cP
    @7
    cP
    @8
    oveq12
    breq2d
    pm5.32i
    bitri
    vr
    cP
    velsn
    3imtr4g
    exp4b
    com23
    ralrimdv
    ralrimivv
    jca
    ex
    cA
    cal
    cS
    @8
    cK
    @10
    @2
    vr
    vq
    vp
    @37
    @35
    snpsub.a
    snpsub.s
    ispsubsp
    sylibrd
    imp
end
