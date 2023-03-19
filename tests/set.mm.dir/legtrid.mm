include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "co.mm"
include "wbr.mm"
include "wo.mm"
include "c2.mm"
include "cle.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "legid.mm"
include "simpr.mm"
include "tgldim0cgr.mm"
include "breqtrd.mm"
include "orcd.mm"
include "cv.mm"
include "wrex.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprl.mm"
include "simplrr.mm"
include "necomd.mm"
include "simplrl.mm"
include "tgbtwncom.mm"
include "simprrl.mm"
include "tgbtwnconn2.mm"
include "simprrr.mm"
include "jca.mm"
include "ad2antrr.mm"
include "axtgsegcon.mm"
include "reximddv.mm"
include "adantllr.mm"
include "tgbtwndiff.mm"
include "r19.29a.mm"
include "andir.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "orbi2i.mm"
include "bitri.mm"
include "rexbii.mm"
include "r19.43.mm"
include "sylib.mm"
include "wb.mm"
include "legov2.mm"
include "legov.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "cbs.mm"
include "tgldimor.mm"
include "mpjaodan.mm"

theorem legtrid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cF: class F
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legid.a: |- ( ph -> A e. P )
  assume legid.b: |- ( ph -> B e. P )
  assume legtrd.c: |- ( ph -> C e. P )
  assume legtrd.d: |- ( ph -> D e. P )


  assert |- ( ph -> ( ( A .- B ) .<_ ( C .- D ) \/ ( C .- D ) .<_ ( A .- B ) ) )

  proof
    wph
    cP
    chash
    cfv
    #
    c1
    wceq
    #
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    c.le
    wbr
    #
    @3
    @2
    c.le
    wbr
    #
    wo
    #
    c2
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    #
    @4
    @5
    @8
    @2
    @2
    @3
    c.le
    @8
    cA
    cB
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    wph
    cG
    cstrkg
    wcel
    #
    @1
    legval.g
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @1
    legid.a
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @1
    legid.b
    adantr
    #
    legid
    @8
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @10
    @12
    @14
    wph
    cC
    cP
    wcel
    #
    @1
    legtrd.c
    adantr
    wph
    @1
    simpr
    wph
    cD
    cP
    wcel
    #
    @1
    legtrd.d
    adantr
    tgldim0cgr
    breqtrd
    orcd
    wph
    @7
    wa
    #
    @6
    cB
    cA
    vy
    cv
    #
    cI
    co
    wcel
    #
    cA
    @18
    c.mi
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    cP
    wrex
    #
    @18
    cA
    cB
    cI
    co
    wcel
    #
    @3
    @20
    wceq
    #
    wa
    #
    vy
    cP
    wrex
    #
    wo
    #
    @17
    @19
    @24
    wo
    #
    @21
    wa
    #
    vy
    cP
    wrex
    #
    @28
    @17
    cA
    cB
    vx
    cv
    #
    cI
    co
    wcel
    #
    cA
    @32
    wne
    #
    wa
    #
    @31
    vx
    cP
    wph
    @32
    cP
    wcel
    #
    @35
    @31
    @7
    wph
    @36
    wa
    #
    @35
    wa
    #
    cA
    @32
    @18
    cI
    co
    wcel
    #
    @21
    wa
    #
    @30
    vy
    cP
    @38
    @18
    cP
    wcel
    #
    @40
    wa
    #
    wa
    #
    @29
    @21
    @43
    @32
    cA
    cB
    @18
    cP
    cG
    cI
    legval.p
    legval.i
    wph
    @9
    @36
    @35
    @42
    legval.g
    ad3antrrr
    #
    @38
    @36
    @42
    wph
    @36
    @35
    simplr
    #
    adantr
    #
    wph
    @11
    @36
    @35
    @42
    legid.a
    ad3antrrr
    #
    wph
    @13
    @36
    @35
    @42
    legid.b
    ad3antrrr
    #
    @38
    @41
    @40
    simprl
    @43
    cA
    @32
    @37
    @33
    @34
    @42
    simplrr
    necomd
    @43
    cB
    cA
    @32
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @44
    @48
    @47
    @46
    @37
    @33
    @34
    @42
    simplrl
    tgbtwncom
    @38
    @41
    @39
    @21
    simprrl
    tgbtwnconn2
    @38
    @41
    @39
    @21
    simprrr
    jca
    @38
    vy
    cC
    cD
    cP
    cG
    cI
    c.mi
    @32
    cA
    legval.p
    legval.d
    legval.i
    wph
    @9
    @36
    @35
    legval.g
    ad2antrr
    @45
    wph
    @11
    @36
    @35
    legid.a
    ad2antrr
    wph
    @15
    @36
    @35
    legtrd.c
    ad2antrr
    wph
    @16
    @36
    @35
    legtrd.d
    ad2antrr
    axtgsegcon
    reximddv
    adantllr
    @17
    cB
    cA
    cP
    cG
    cI
    c.mi
    vx
    legval.p
    legval.d
    legval.i
    wph
    @9
    @7
    legval.g
    adantr
    wph
    @13
    @7
    legid.b
    adantr
    wph
    @11
    @7
    legid.a
    adantr
    wph
    @7
    simpr
    tgbtwndiff
    r19.29a
    @31
    @22
    @26
    wo
    #
    vy
    cP
    wrex
    @28
    @30
    @49
    vy
    cP
    @30
    @22
    @24
    @21
    wa
    #
    wo
    @49
    @19
    @24
    @21
    andir
    @50
    @26
    @22
    @21
    @25
    @24
    @20
    @3
    eqcom
    anbi2i
    orbi2i
    bitri
    rexbii
    @22
    @26
    vy
    cP
    r19.43
    bitri
    sylib
    wph
    @6
    @28
    wb
    @7
    wph
    @4
    @23
    @5
    @27
    wph
    vy
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.b
    legtrd.c
    legtrd.d
    legov2
    wph
    vy
    cC
    cD
    cA
    cB
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legtrd.c
    legtrd.d
    legid.a
    legid.b
    legov
    orbi12d
    adantr
    mpbird
    wph
    cA
    cP
    cbs
    cG
    legval.p
    legid.a
    tgldimor
    mpjaodan
end
