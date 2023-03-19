include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "mircl.mm"
include "simpr.mm"
include "mirbtwn.mm"
include "tgbtwnintr.mm"
include "wceq.mm"
include "tgbtwntriv2.mm"
include "fveq2d.mm"
include "mircinv.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "adantlr.mm"
include "wne.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "tgbtwncom.mm"
include "tgbtwnouttr2.mm"
include "pm2.61dane.mm"
include "mpjaodan.mm"

theorem mirconn
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirconn.m: |- M = ( S ` A )
  assume mirconn.a: |- ( ph -> A e. P )
  assume mirconn.x: |- ( ph -> X e. P )
  assume mirconn.y: |- ( ph -> Y e. P )
  assume mirconn.1: |- ( ph -> ( X e. ( A I Y ) \/ Y e. ( A I X ) ) )


  assert |- ( ph -> A e. ( X I ( M ` Y ) ) )

  proof
    wph
    cX
    cA
    cY
    cI
    co
    wcel
    #
    cA
    cX
    cY
    cM
    cfv
    #
    cI
    co
    #
    wcel
    #
    cY
    cA
    cX
    cI
    co
    wcel
    #
    wph
    @0
    wa
    cX
    cA
    @1
    cY
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    mirval.g
    adantr
    wph
    cX
    cP
    wcel
    #
    @0
    mirconn.x
    adantr
    wph
    cA
    cP
    wcel
    #
    @0
    mirconn.a
    adantr
    wph
    @1
    cP
    wcel
    #
    @0
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirconn.a
    mirconn.m
    mirconn.y
    mircl
    #
    adantr
    wph
    cY
    cP
    wcel
    #
    @0
    mirconn.y
    adantr
    wph
    @0
    simpr
    wph
    cA
    @1
    cY
    cI
    co
    wcel
    @0
    wph
    cA
    cY
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
    mirconn.a
    mirconn.m
    mirconn.y
    mirbtwn
    #
    adantr
    tgbtwnintr
    wph
    @4
    wa
    #
    @3
    cY
    cA
    wph
    cY
    cA
    wceq
    #
    @3
    @4
    wph
    @13
    wa
    #
    cA
    cX
    cA
    cI
    co
    #
    @2
    wph
    cA
    @15
    wcel
    @13
    wph
    cX
    cA
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirconn.x
    mirconn.a
    tgbtwntriv2
    adantr
    @14
    @1
    cA
    cX
    cI
    @14
    @1
    cA
    cM
    cfv
    #
    cA
    @14
    cY
    cA
    cM
    wph
    @13
    simpr
    fveq2d
    wph
    @16
    cA
    wceq
    @13
    wph
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
    mirval.g
    mirconn.a
    mirconn.m
    mircinv
    adantr
    eqtrd
    oveq2d
    eleqtrrd
    adantlr
    @12
    cY
    cA
    wne
    #
    wa
    #
    cX
    cY
    cA
    @1
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    wph
    @5
    @4
    @17
    mirval.g
    ad2antrr
    #
    wph
    @6
    @4
    @17
    mirconn.x
    ad2antrr
    #
    wph
    @10
    @4
    @17
    mirconn.y
    ad2antrr
    #
    wph
    @7
    @4
    @17
    mirconn.a
    ad2antrr
    #
    wph
    @8
    @4
    @17
    @9
    ad2antrr
    @12
    @17
    simpr
    @18
    cA
    cY
    cX
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @19
    @22
    @21
    @20
    wph
    @4
    @17
    simplr
    tgbtwncom
    wph
    cA
    cY
    @1
    cI
    co
    wcel
    @4
    @17
    wph
    @1
    cA
    cY
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @9
    mirconn.a
    mirconn.y
    @11
    tgbtwncom
    ad2antrr
    tgbtwnouttr2
    pm2.61dane
    mirconn.1
    mpjaodan
end
