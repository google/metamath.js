include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "cds.mm"
include "eqid.mm"
include "tgbtwntriv2.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "olcd.mm"
include "wne.mm"
include "w3o.mm"
include "tglngne.mm"
include "tgellng.mm"
include "mpbid.mm"
include "df-3or.mm"
include "sylib.mm"
include "w3a.mm"
include "wb.mm"
include "cstrkg.mm"
include "ishlg.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "jca.mm"
include "biantrurd.mm"
include "tgbtwncomb.mm"
include "orbi12d.mm"
include "3bitr2d.mm"
include "orbi1d.mm"
include "mpbird.mm"
include "pm2.61dane.mm"

theorem lnhl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume lnhl.l: |- L = ( LineG ` G )
  assume lnhl.1: |- ( ph -> C e. ( A L B ) )


  assert |- ( ph -> ( C ( K ` B ) A \/ B e. ( A I C ) ) )

  proof
    wph
    cC
    cA
    cB
    cK
    cfv
    wbr
    #
    cB
    cA
    cC
    cI
    co
    #
    wcel
    #
    wo
    #
    cC
    cB
    wph
    cC
    cB
    wceq
    #
    wa
    #
    @2
    @0
    @5
    cC
    cB
    @1
    wph
    @4
    simpr
    wph
    cC
    @1
    wcel
    @4
    wph
    cA
    cC
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @6
    eqid
    #
    ishlg.i
    hlln.1
    ishlg.a
    ishlg.c
    tgbtwntriv2
    adantr
    eqeltrrd
    olcd
    wph
    cC
    cB
    wne
    #
    wa
    #
    @3
    cC
    cA
    cB
    cI
    co
    wcel
    #
    cA
    cC
    cB
    cI
    co
    wcel
    #
    wo
    #
    @2
    wo
    #
    wph
    @13
    @8
    wph
    @10
    @11
    @2
    w3o
    #
    @13
    wph
    cC
    cA
    cB
    cL
    co
    wcel
    @14
    lnhl.1
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    ishlg.p
    lnhl.l
    ishlg.i
    hlln.1
    ishlg.a
    ishlg.b
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    ishlg.p
    lnhl.l
    ishlg.i
    hlln.1
    ishlg.a
    ishlg.b
    lnhl.1
    tglngne
    #
    ishlg.c
    tgellng
    mpbid
    @10
    @11
    @2
    df-3or
    sylib
    adantr
    @9
    @0
    @12
    @2
    @9
    @0
    @8
    cA
    cB
    wne
    #
    wa
    #
    cC
    cB
    cA
    cI
    co
    wcel
    #
    cA
    cB
    cC
    cI
    co
    wcel
    #
    wo
    #
    wa
    #
    @20
    @12
    @9
    @0
    @8
    @16
    @20
    w3a
    #
    @21
    wph
    @0
    @22
    wb
    @8
    wph
    cC
    cA
    cB
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.c
    ishlg.a
    ishlg.b
    hlln.1
    ishlg
    adantr
    @8
    @16
    @20
    df-3an
    syl6bb
    @9
    @17
    @20
    @9
    @8
    @16
    wph
    @8
    simpr
    wph
    @16
    @8
    @15
    adantr
    jca
    biantrurd
    @9
    @18
    @10
    @19
    @11
    @9
    cB
    cC
    cA
    cP
    cG
    cI
    @6
    ishlg.p
    @7
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    @8
    hlln.1
    adantr
    #
    wph
    cB
    cP
    wcel
    @8
    ishlg.b
    adantr
    #
    wph
    cC
    cP
    wcel
    @8
    ishlg.c
    adantr
    #
    wph
    cA
    cP
    wcel
    @8
    ishlg.a
    adantr
    #
    tgbtwncomb
    @9
    cB
    cA
    cC
    cP
    cG
    cI
    @6
    ishlg.p
    @7
    ishlg.i
    @23
    @24
    @26
    @25
    tgbtwncomb
    orbi12d
    3bitr2d
    orbi1d
    mpbird
    pm2.61dane
end
