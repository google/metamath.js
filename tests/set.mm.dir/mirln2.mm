include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "tglnpt.mm"
include "mirinv.mm"
include "biimpa.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "co.mm"
include "cstrkg.mm"
include "simpr.mm"
include "mirbtwn.mm"
include "btwnlng1.mm"
include "crn.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "pm2.61dane.mm"

theorem mirln2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirln2.m: |- M = ( S ` A )
  assume mirln2.d: |- ( ph -> D e. ran L )
  assume mirln2.a: |- ( ph -> A e. P )
  assume mirln2.1: |- ( ph -> B e. D )
  assume mirln2.2: |- ( ph -> ( M ` B ) e. D )


  assert |- ( ph -> A e. D )

  proof
    wph
    cA
    cD
    wcel
    cB
    cM
    cfv
    #
    cB
    wph
    @0
    cB
    wceq
    #
    wa
    cA
    cB
    cD
    wph
    @1
    cA
    cB
    wceq
    wph
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
    mirval.g
    mirln2.a
    mirln2.m
    wph
    cD
    cP
    cG
    cI
    cL
    cB
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    mirln2.d
    mirln2.1
    tglnpt
    #
    mirinv
    biimpa
    wph
    cB
    cD
    wcel
    #
    @1
    mirln2.1
    adantr
    eqeltrd
    wph
    @0
    cB
    wne
    #
    wa
    #
    cA
    @0
    cB
    cL
    co
    cD
    @5
    cP
    cG
    cI
    cL
    @0
    cB
    cA
    mirval.p
    mirval.i
    mirval.l
    wph
    cG
    cstrkg
    wcel
    @4
    mirval.g
    adantr
    #
    wph
    @0
    cP
    wcel
    @4
    wph
    cD
    cP
    cG
    cI
    cL
    @0
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    mirln2.d
    mirln2.2
    tglnpt
    adantr
    #
    wph
    cB
    cP
    wcel
    @4
    @2
    adantr
    #
    wph
    cA
    cP
    wcel
    @4
    mirln2.a
    adantr
    #
    wph
    @4
    simpr
    #
    @5
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
    @6
    @9
    mirln2.m
    @8
    mirbtwn
    btwnlng1
    @5
    cD
    cP
    @0
    cB
    cG
    cI
    cL
    mirval.p
    mirval.i
    mirval.l
    @6
    @7
    @8
    @10
    @10
    wph
    cD
    cL
    crn
    wcel
    @4
    mirln2.d
    adantr
    wph
    @0
    cD
    wcel
    @4
    mirln2.2
    adantr
    wph
    @3
    @4
    mirln2.1
    adantr
    tglinethru
    eleqtrrd
    pm2.61dane
end
