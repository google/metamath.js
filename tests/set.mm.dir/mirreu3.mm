include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "adantr.mm"
include "eqidd.mm"
include "simpr.mm"
include "cstrkg.mm"
include "tgbtwntriv2.mm"
include "eqeltrrd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "simprll.mm"
include "simpllr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "axtgcgrid.mm"
include "simplrr.mm"
include "simprrl.mm"
include "eqtr3d.mm"
include "ex.mm"
include "ralrimivva.mm"
include "jca.mm"
include "wne.mm"
include "axtgsegcon.mm"
include "wb.mm"
include "ancom.mm"
include "tgbtwncomb.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "simprlr.mm"
include "tgbtwncom.mm"
include "simprrr.mm"
include "tgsegconeq.mm"
include "pm2.61dane.mm"
include "reu4.mm"
include "sylibr.mm"

theorem mirreu3
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let vb: setvar b
  let vc: setvar c
  assume mirreu.p: |- P = ( Base ` G )
  assume mirreu.d: |- .- = ( dist ` G )
  assume mirreu.i: |- I = ( Itv ` G )
  assume mirreu.g: |- ( ph -> G e. TarskiG )
  assume mirreu.a: |- ( ph -> A e. P )
  assume mirreu.m: |- ( ph -> M e. P )

  disjoint .- b
  disjoint A b
  disjoint I b
  disjoint M b
  disjoint P b
  disjoint b ph
  disjoint b c
  disjoint .- c
  disjoint A c
  disjoint I c
  disjoint M c
  disjoint P c
  disjoint c ph
  assert |- ( ph -> E! b e. P ( ( M .- b ) = ( M .- A ) /\ M e. ( b I A ) ) )

  proof
    wph
    cM
    vb
    cv
    #
    c.mi
    co
    #
    cM
    cA
    c.mi
    co
    #
    wceq
    #
    cM
    @0
    cA
    cI
    co
    #
    wcel
    #
    wa
    #
    vb
    cP
    wrex
    #
    @6
    cM
    vc
    cv
    #
    c.mi
    co
    #
    @2
    wceq
    #
    cM
    @8
    cA
    cI
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    @0
    @8
    wceq
    #
    wi
    #
    vc
    cP
    wral
    vb
    cP
    wral
    #
    wa
    #
    @6
    vb
    cP
    wreu
    wph
    @18
    cA
    cM
    wph
    cA
    cM
    wceq
    #
    wa
    #
    @7
    @17
    @20
    cA
    cP
    wcel
    #
    @2
    @2
    wceq
    #
    cM
    cA
    cA
    cI
    co
    #
    wcel
    #
    @7
    wph
    @21
    @19
    mirreu.a
    adantr
    #
    @20
    @2
    eqidd
    @20
    cA
    cM
    @23
    wph
    @19
    simpr
    @20
    cA
    cA
    cP
    cG
    cI
    c.mi
    mirreu.p
    mirreu.d
    mirreu.i
    wph
    cG
    cstrkg
    wcel
    #
    @19
    mirreu.g
    adantr
    @25
    @25
    tgbtwntriv2
    eqeltrrd
    @6
    @22
    @24
    wa
    vb
    cA
    cP
    @0
    cA
    wceq
    #
    @3
    @22
    @5
    @24
    @27
    @1
    @2
    @2
    @0
    cA
    cM
    c.mi
    oveq2
    eqeq1d
    @27
    @4
    @23
    cM
    @0
    cA
    cA
    cI
    oveq1
    eleq2d
    anbi12d
    rspcev
    syl12anc
    @20
    @16
    vb
    vc
    cP
    cP
    @20
    @0
    cP
    wcel
    #
    @8
    cP
    wcel
    #
    wa
    #
    wa
    #
    @14
    @15
    @31
    @14
    wa
    #
    cM
    @0
    @8
    @32
    cP
    cG
    cI
    c.mi
    cM
    @0
    cM
    mirreu.p
    mirreu.d
    mirreu.i
    wph
    @26
    @19
    @30
    @14
    mirreu.g
    ad3antrrr
    #
    wph
    cM
    cP
    wcel
    #
    @19
    @30
    @14
    mirreu.m
    ad3antrrr
    #
    @20
    @28
    @29
    @14
    simplrl
    @35
    @32
    @1
    @2
    cM
    cM
    c.mi
    co
    #
    @31
    @3
    @5
    @13
    simprll
    @32
    cA
    cM
    cM
    c.mi
    wph
    @19
    @30
    @14
    simpllr
    oveq2d
    #
    eqtrd
    axtgcgrid
    @32
    cP
    cG
    cI
    c.mi
    cM
    @8
    cM
    mirreu.p
    mirreu.d
    mirreu.i
    @33
    @35
    @20
    @28
    @29
    @14
    simplrr
    @35
    @32
    @9
    @2
    @36
    @31
    @6
    @10
    @12
    simprrl
    @37
    eqtrd
    axtgcgrid
    eqtr3d
    ex
    ralrimivva
    jca
    wph
    cA
    cM
    wne
    #
    wa
    #
    @7
    @17
    @39
    cM
    cA
    @0
    cI
    co
    wcel
    #
    @3
    wa
    #
    vb
    cP
    wrex
    #
    @7
    @39
    vb
    cM
    cA
    cP
    cG
    cI
    c.mi
    cA
    cM
    mirreu.p
    mirreu.d
    mirreu.i
    wph
    @26
    @38
    mirreu.g
    adantr
    wph
    @21
    @38
    mirreu.a
    adantr
    #
    wph
    @34
    @38
    mirreu.m
    adantr
    #
    @44
    @43
    axtgsegcon
    wph
    @42
    @7
    wb
    @38
    wph
    @41
    @6
    vb
    cP
    @41
    @3
    @40
    wa
    wph
    @28
    wa
    #
    @6
    @40
    @3
    ancom
    @45
    @40
    @5
    @3
    @45
    cA
    cM
    @0
    cP
    cG
    cI
    c.mi
    mirreu.p
    mirreu.d
    mirreu.i
    wph
    @26
    @28
    mirreu.g
    adantr
    wph
    @21
    @28
    mirreu.a
    adantr
    wph
    @34
    @28
    mirreu.m
    adantr
    wph
    @28
    simpr
    tgbtwncomb
    anbi2d
    syl5bb
    rexbidva
    adantr
    mpbid
    @39
    @16
    vb
    vc
    cP
    cP
    @39
    @30
    wa
    #
    @14
    @15
    @46
    @14
    wa
    #
    cM
    cM
    cA
    cA
    cP
    @0
    @8
    cG
    cI
    c.mi
    mirreu.p
    mirreu.d
    mirreu.i
    wph
    @26
    @38
    @30
    @14
    mirreu.g
    ad3antrrr
    #
    wph
    @34
    @38
    @30
    @14
    mirreu.m
    ad3antrrr
    #
    @49
    wph
    @21
    @38
    @30
    @14
    mirreu.a
    ad3antrrr
    #
    @50
    @39
    @28
    @29
    @14
    simplrl
    #
    @39
    @28
    @29
    @14
    simplrr
    #
    wph
    @38
    @30
    @14
    simpllr
    @47
    @0
    cM
    cA
    cP
    cG
    cI
    c.mi
    mirreu.p
    mirreu.d
    mirreu.i
    @48
    @51
    @49
    @50
    @46
    @3
    @5
    @13
    simprlr
    tgbtwncom
    @47
    @8
    cM
    cA
    cP
    cG
    cI
    c.mi
    mirreu.p
    mirreu.d
    mirreu.i
    @48
    @52
    @49
    @50
    @46
    @6
    @10
    @12
    simprrr
    tgbtwncom
    @46
    @3
    @5
    @13
    simprll
    @46
    @6
    @10
    @12
    simprrl
    tgsegconeq
    ex
    ralrimivva
    jca
    pm2.61dane
    @6
    @13
    vb
    vc
    cP
    @15
    @3
    @10
    @5
    @12
    @15
    @1
    @9
    @2
    @0
    @8
    cM
    c.mi
    oveq2
    eqeq1d
    @15
    @4
    @11
    cM
    @0
    @8
    cA
    cI
    oveq1
    eleq2d
    anbi12d
    reu4
    sylibr
end
