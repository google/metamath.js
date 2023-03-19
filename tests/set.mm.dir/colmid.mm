include "cfv.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "simpr.mm"
include "olcd.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "eqcomd.mm"
include "tgbtwncom.mm"
include "ismir.mm"
include "orcd.mm"
include "adantr.mm"
include "tgbtwntriv1.mm"
include "tgcgrcomlr.mm"
include "eqidd.mm"
include "tgcgrsub.mm"
include "axtgcgrid.mm"
include "adantlr.mm"
include "w3o.mm"
include "wn.mm"
include "df-ne.mm"
include "orcomd.mm"
include "orcanai.mm"
include "sylan2b.mm"
include "tgellng.mm"
include "mpbid.mm"
include "mpjao3dan.mm"
include "pm2.61dane.mm"

theorem colmid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cX: class X
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume colmid.m: |- M = ( S ` X )
  assume colmid.a: |- ( ph -> A e. P )
  assume colmid.b: |- ( ph -> B e. P )
  assume colmid.x: |- ( ph -> X e. P )
  assume colmid.c: |- ( ph -> ( X e. ( A L B ) \/ A = B ) )
  assume colmid.d: |- ( ph -> ( X .- A ) = ( X .- B ) )


  assert |- ( ph -> ( B = ( M ` A ) \/ A = B ) )

  proof
    wph
    cB
    cA
    cM
    cfv
    wceq
    #
    cA
    cB
    wceq
    #
    wo
    #
    cA
    cB
    wph
    @1
    wa
    @1
    @0
    wph
    @1
    simpr
    olcd
    wph
    cA
    cB
    wne
    #
    wa
    #
    cX
    cA
    cB
    cI
    co
    wcel
    #
    @2
    cA
    cX
    cB
    cI
    co
    wcel
    #
    cB
    cA
    cX
    cI
    co
    wcel
    #
    @4
    @5
    wa
    #
    @0
    @1
    @8
    cX
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    cG
    cstrkg
    wcel
    #
    @3
    @5
    mirval.g
    ad2antrr
    #
    wph
    cX
    cP
    wcel
    #
    @3
    @5
    colmid.x
    ad2antrr
    #
    colmid.m
    wph
    cA
    cP
    wcel
    #
    @3
    @5
    colmid.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    #
    @3
    @5
    colmid.b
    ad2antrr
    #
    @8
    cX
    cA
    c.mi
    co
    #
    cX
    cB
    c.mi
    co
    #
    wph
    @17
    @18
    wceq
    @3
    @5
    colmid.d
    ad2antrr
    eqcomd
    @8
    cA
    cX
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @10
    @14
    @12
    @16
    @4
    @5
    simpr
    tgbtwncom
    ismir
    orcd
    @4
    @6
    wa
    @1
    @0
    wph
    @6
    @1
    @3
    wph
    @6
    wa
    #
    cB
    cA
    @19
    cP
    cG
    cI
    c.mi
    cB
    cA
    cA
    mirval.p
    mirval.d
    mirval.i
    wph
    @9
    @6
    mirval.g
    adantr
    #
    wph
    @15
    @6
    colmid.b
    adantr
    #
    wph
    @13
    @6
    colmid.a
    adantr
    #
    @22
    @19
    cB
    cA
    cX
    cA
    cP
    cA
    cX
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @20
    @21
    @22
    wph
    @11
    @6
    colmid.x
    adantr
    #
    @22
    @22
    @23
    @19
    cX
    cA
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @20
    @23
    @22
    @21
    wph
    @6
    simpr
    tgbtwncom
    @19
    cA
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @20
    @22
    @23
    tgbtwntriv1
    @19
    cA
    cX
    c.mi
    co
    #
    cB
    cX
    c.mi
    co
    #
    wph
    @24
    @25
    wceq
    #
    @6
    wph
    cX
    cA
    cX
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    colmid.x
    colmid.a
    colmid.x
    colmid.b
    colmid.d
    tgcgrcomlr
    #
    adantr
    eqcomd
    @19
    @24
    eqidd
    tgcgrsub
    axtgcgrid
    eqcomd
    adantlr
    olcd
    @4
    @7
    wa
    @1
    @0
    wph
    @7
    @1
    @3
    wph
    @7
    wa
    #
    cP
    cG
    cI
    c.mi
    cA
    cB
    cB
    mirval.p
    mirval.d
    mirval.i
    wph
    @9
    @7
    mirval.g
    adantr
    #
    wph
    @13
    @7
    colmid.a
    adantr
    #
    wph
    @15
    @7
    colmid.b
    adantr
    #
    @31
    @28
    cA
    cB
    cX
    cB
    cP
    cB
    cX
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @29
    @30
    @31
    wph
    @11
    @7
    colmid.x
    adantr
    #
    @31
    @31
    @32
    wph
    @7
    simpr
    @28
    cB
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @29
    @31
    @32
    tgbtwntriv1
    wph
    @26
    @7
    @27
    adantr
    @28
    @25
    eqidd
    tgcgrsub
    axtgcgrid
    adantlr
    olcd
    @4
    cX
    cA
    cB
    cL
    co
    wcel
    #
    @5
    @6
    @7
    w3o
    @3
    wph
    @1
    wn
    @33
    cA
    cB
    df-ne
    wph
    @1
    @33
    wph
    @33
    @1
    colmid.c
    orcomd
    orcanai
    sylan2b
    @4
    cP
    cG
    cI
    cL
    cA
    cB
    cX
    mirval.p
    mirval.l
    mirval.i
    wph
    @9
    @3
    mirval.g
    adantr
    wph
    @13
    @3
    colmid.a
    adantr
    wph
    @15
    @3
    colmid.b
    adantr
    wph
    @3
    simpr
    wph
    @11
    @3
    colmid.x
    adantr
    tgellng
    mpbid
    mpjao3dan
    pm2.61dane
end
