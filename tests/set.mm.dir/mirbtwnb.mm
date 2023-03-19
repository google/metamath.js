include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "mirbtwni.mm"
include "mirf.mm"
include "ffvelrnd.mm"
include "wb.mm"
include "mirmir.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "mpbid.mm"
include "impbida.mm"

theorem mirbtwnb
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
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vg: setvar g
  let va: setvar a
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume miriso.1: |- ( ph -> X e. P )
  assume miriso.2: |- ( ph -> Y e. P )
  assume mirbtwnb.z: |- ( ph -> Z e. P )


  assert |- ( ph -> ( Y e. ( X I Z ) <-> ( M ` Y ) e. ( ( M ` X ) I ( M ` Z ) ) ) )

  proof
    wph
    cY
    cX
    cZ
    cI
    co
    #
    wcel
    #
    cY
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cZ
    cM
    cfv
    #
    cI
    co
    wcel
    #
    wph
    @1
    wa
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cX
    cY
    cZ
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
    mirval.a
    adantr
    mirfv.m
    wph
    cX
    cP
    wcel
    #
    @1
    miriso.1
    adantr
    wph
    cY
    cP
    wcel
    #
    @1
    miriso.2
    adantr
    wph
    cZ
    cP
    wcel
    #
    @1
    mirbtwnb.z
    adantr
    wph
    @1
    simpr
    mirbtwni
    wph
    @5
    wa
    #
    @2
    cM
    cfv
    #
    @3
    cM
    cfv
    #
    @4
    cM
    cfv
    #
    cI
    co
    #
    wcel
    #
    @1
    @11
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    @3
    @2
    @4
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    @6
    @5
    mirval.g
    adantr
    #
    wph
    @7
    @5
    mirval.a
    adantr
    #
    mirfv.m
    @11
    cP
    cP
    cX
    cM
    @11
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
    @17
    @18
    mirfv.m
    mirf
    #
    wph
    @8
    @5
    miriso.1
    adantr
    ffvelrnd
    @11
    cP
    cP
    cY
    cM
    @19
    wph
    @9
    @5
    miriso.2
    adantr
    ffvelrnd
    @11
    cP
    cP
    cZ
    cM
    @19
    wph
    @10
    @5
    mirbtwnb.z
    adantr
    ffvelrnd
    wph
    @5
    simpr
    mirbtwni
    wph
    @16
    @1
    wb
    @5
    wph
    @12
    cY
    @15
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
    mirval.a
    mirfv.m
    miriso.2
    mirmir
    wph
    @13
    cX
    @14
    cZ
    cI
    wph
    cA
    cX
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
    mirval.a
    mirfv.m
    miriso.1
    mirmir
    wph
    cA
    cZ
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
    mirval.a
    mirfv.m
    mirbtwnb.z
    mirmir
    oveq12d
    eleq12d
    adantr
    mpbid
    impbida
end
