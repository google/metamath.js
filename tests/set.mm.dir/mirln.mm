include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "cstrkg.mm"
include "adantr.mm"
include "tglnpt.mm"
include "mircinv.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "wne.mm"
include "co.mm"
include "mircl.mm"
include "mirbtwn.mm"
include "btwnlng2.mm"
include "crn.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "pm2.61dane.mm"

theorem mirln
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
  assume mirln.m: |- M = ( S ` A )
  assume mirln.1: |- ( ph -> D e. ran L )
  assume mirln.a: |- ( ph -> A e. D )
  assume mirln.b: |- ( ph -> B e. D )


  assert |- ( ph -> ( M ` B ) e. D )

  proof
    wph
    cB
    cM
    cfv
    #
    cD
    wcel
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    wa
    #
    @0
    cA
    cD
    @2
    cA
    cM
    cfv
    @0
    cA
    @2
    cA
    cB
    cM
    wph
    @1
    simpr
    fveq2d
    @2
    cA
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
    @1
    mirval.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @1
    wph
    cD
    cP
    cG
    cI
    cL
    cA
    mirval.p
    mirval.l
    mirval.i
    mirval.g
    mirln.1
    mirln.a
    tglnpt
    #
    adantr
    mirln.m
    mircinv
    eqtr3d
    wph
    cA
    cD
    wcel
    #
    @1
    mirln.a
    adantr
    eqeltrd
    wph
    cA
    cB
    wne
    #
    wa
    #
    @0
    cA
    cB
    cL
    co
    cD
    @8
    cP
    cG
    cI
    cL
    cA
    cB
    @0
    mirval.p
    mirval.i
    mirval.l
    wph
    @3
    @7
    mirval.g
    adantr
    #
    wph
    @4
    @7
    @5
    adantr
    #
    wph
    cB
    cP
    wcel
    @7
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
    mirln.1
    mirln.b
    tglnpt
    #
    adantr
    #
    @8
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    @9
    @10
    mirln.m
    @12
    mircl
    wph
    @7
    simpr
    #
    wph
    cA
    @0
    cB
    cI
    co
    wcel
    @7
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
    @5
    mirln.m
    @11
    mirbtwn
    adantr
    btwnlng2
    @8
    cD
    cP
    cA
    cB
    cG
    cI
    cL
    mirval.p
    mirval.i
    mirval.l
    @9
    @10
    @12
    @13
    @13
    wph
    cD
    cL
    crn
    wcel
    @7
    mirln.1
    adantr
    wph
    @6
    @7
    mirln.a
    adantr
    wph
    cB
    cD
    wcel
    @7
    mirln.b
    adantr
    tglinethru
    eleqtrrd
    pm2.61dane
end
