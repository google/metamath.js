include "co.mm"
include "wne.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "ncolne1.mm"
include "tglinerflx1.mm"
include "adantr.mm"
include "simplr.mm"
include "cstrkg.mm"
include "simpr.mm"
include "tglngne.mm"
include "adantlr.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "wo.mm"
include "ad2antrr.mm"
include "pm2.46.mm"
include "syl.mm"
include "neqned.mm"
include "eleqtrrd.mm"
include "lnrot1.mm"
include "orcd.mm"
include "pm2.61dane.mm"

theorem tglineneq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vx: setvar x
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglineinteq.a: |- ( ph -> A e. P )
  assume tglineinteq.b: |- ( ph -> B e. P )
  assume tglineinteq.c: |- ( ph -> C e. P )
  assume tglineinteq.d: |- ( ph -> D e. P )
  assume tglineinteq.e: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )


  assert |- ( ph -> ( A L B ) =/= ( C L D ) )

  proof
    wph
    cA
    cB
    cL
    co
    #
    cC
    cD
    cL
    co
    #
    wne
    #
    cC
    cD
    wph
    cC
    cD
    wceq
    #
    wa
    #
    cA
    @0
    wcel
    #
    cA
    @1
    wcel
    #
    wn
    @2
    wph
    @5
    @3
    wph
    cP
    cA
    cB
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    tglineinteq.c
    tglineinteq.e
    ncolne1
    tglinerflx1
    adantr
    @4
    @6
    @3
    wph
    @3
    @6
    simplr
    @4
    @6
    wa
    cC
    cD
    wph
    @6
    cC
    cD
    wne
    #
    @3
    wph
    @6
    wa
    cP
    cG
    cI
    cL
    cC
    cD
    cA
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    wph
    cG
    cstrkg
    wcel
    #
    @6
    tglineintmo.g
    adantr
    wph
    cC
    cP
    wcel
    #
    @6
    tglineinteq.c
    adantr
    wph
    cD
    cP
    wcel
    #
    @6
    tglineinteq.d
    adantr
    wph
    @6
    simpr
    tglngne
    adantlr
    neneqd
    pm2.65da
    cA
    @0
    @1
    nelne1
    syl2anc
    wph
    @7
    wa
    #
    @0
    @1
    @11
    @0
    @1
    wceq
    #
    cA
    cB
    cC
    cL
    co
    wcel
    #
    cB
    cC
    wceq
    #
    wo
    #
    @11
    @12
    wa
    #
    @13
    @14
    @16
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @8
    @7
    @12
    tglineintmo.g
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    @7
    @12
    tglineinteq.b
    ad2antrr
    #
    wph
    @9
    @7
    @12
    tglineinteq.c
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    @7
    @12
    tglineinteq.a
    ad2antrr
    #
    wph
    cB
    cC
    wne
    @7
    @12
    wph
    cB
    cC
    wph
    @15
    wn
    #
    @14
    wn
    tglineinteq.e
    @13
    @14
    pm2.46
    syl
    neqned
    ad2antrr
    @16
    cC
    @1
    @0
    @16
    cP
    cC
    cD
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @17
    @19
    wph
    @10
    @7
    @12
    tglineinteq.d
    ad2antrr
    wph
    @7
    @12
    simplr
    tglinerflx1
    @11
    @12
    simpr
    eleqtrrd
    #
    @16
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    @17
    @20
    @18
    @22
    tglngne
    lnrot1
    orcd
    wph
    @21
    @7
    @12
    tglineinteq.e
    ad2antrr
    pm2.65da
    neqned
    pm2.61dane
end
