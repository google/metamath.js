include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "mireq.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp1d.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "simp2d.mm"
include "simp3d.mm"
include "mirbtwni.mm"
include "ex.mm"
include "orim12d.mm"
include "mpd.mm"
include "3jca.mm"
include "mircl.mm"
include "mpbird.mm"

theorem mirhl
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirhl.m: |- M = ( S ` A )
  assume mirhl.k: |- K = ( hlG ` G )
  assume mirhl.a: |- ( ph -> A e. P )
  assume mirhl.x: |- ( ph -> X e. P )
  assume mirhl.y: |- ( ph -> Y e. P )
  assume mirhl.z: |- ( ph -> Z e. P )
  assume mirhl.1: |- ( ph -> X ( K ` Z ) Y )


  assert |- ( ph -> ( M ` X ) ( K ` ( M ` Z ) ) ( M ` Y ) )

  proof
    wph
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    cZ
    cM
    cfv
    #
    cK
    cfv
    wbr
    @0
    @2
    wne
    #
    @1
    @2
    wne
    #
    @0
    @2
    @1
    cI
    co
    wcel
    #
    @1
    @2
    @0
    cI
    co
    wcel
    #
    wo
    #
    w3a
    wph
    @3
    @4
    @7
    wph
    @0
    @2
    wph
    @0
    @2
    wceq
    #
    cX
    cZ
    wceq
    wph
    @8
    wa
    #
    cA
    cX
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
    wph
    cG
    cstrkg
    wcel
    #
    @8
    mirval.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @8
    mirhl.a
    adantr
    mirhl.m
    wph
    cX
    cP
    wcel
    #
    @8
    mirhl.x
    adantr
    wph
    cZ
    cP
    wcel
    #
    @8
    mirhl.z
    adantr
    wph
    @8
    simpr
    mireq
    @9
    cX
    cZ
    wph
    cX
    cZ
    wne
    #
    @8
    wph
    @14
    cY
    cZ
    wne
    #
    cX
    cZ
    cY
    cI
    co
    wcel
    #
    cY
    cZ
    cX
    cI
    co
    wcel
    #
    wo
    #
    wph
    cX
    cY
    cZ
    cK
    cfv
    wbr
    @14
    @15
    @18
    w3a
    mirhl.1
    wph
    cX
    cY
    cZ
    cP
    cG
    cI
    cK
    cstrkg
    mirval.p
    mirval.i
    mirhl.k
    mirhl.x
    mirhl.y
    mirhl.z
    mirval.g
    ishlg
    mpbid
    #
    simp1d
    adantr
    neneqd
    pm2.65da
    neqned
    wph
    @1
    @2
    wph
    @1
    @2
    wceq
    #
    cY
    cZ
    wceq
    wph
    @20
    wa
    #
    cA
    cY
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
    wph
    @10
    @20
    mirval.g
    adantr
    wph
    @11
    @20
    mirhl.a
    adantr
    mirhl.m
    wph
    cY
    cP
    wcel
    #
    @20
    mirhl.y
    adantr
    wph
    @13
    @20
    mirhl.z
    adantr
    wph
    @20
    simpr
    mireq
    @21
    cY
    cZ
    wph
    @15
    @20
    wph
    @14
    @15
    @18
    @19
    simp2d
    adantr
    neneqd
    pm2.65da
    neqned
    wph
    @18
    @7
    wph
    @14
    @15
    @18
    @19
    simp3d
    wph
    @16
    @5
    @17
    @6
    wph
    @16
    @5
    wph
    @16
    wa
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cZ
    cX
    cY
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    @10
    @16
    mirval.g
    adantr
    wph
    @11
    @16
    mirhl.a
    adantr
    mirhl.m
    wph
    @13
    @16
    mirhl.z
    adantr
    wph
    @12
    @16
    mirhl.x
    adantr
    wph
    @22
    @16
    mirhl.y
    adantr
    wph
    @16
    simpr
    mirbtwni
    ex
    wph
    @17
    @6
    wph
    @17
    wa
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cZ
    cY
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    @10
    @17
    mirval.g
    adantr
    wph
    @11
    @17
    mirhl.a
    adantr
    mirhl.m
    wph
    @13
    @17
    mirhl.z
    adantr
    wph
    @22
    @17
    mirhl.y
    adantr
    wph
    @12
    @17
    mirhl.x
    adantr
    wph
    @17
    simpr
    mirbtwni
    ex
    orim12d
    mpd
    3jca
    wph
    @0
    @1
    @2
    cP
    cG
    cI
    cK
    cstrkg
    mirval.p
    mirval.i
    mirhl.k
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirhl.a
    mirhl.m
    mirhl.x
    mircl
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
    mirhl.a
    mirhl.m
    mirhl.y
    mircl
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cZ
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirhl.a
    mirhl.m
    mirhl.z
    mircl
    mirval.g
    ishlg
    mpbird
end
