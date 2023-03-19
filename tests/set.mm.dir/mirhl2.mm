include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "mircl.mm"
include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "mircinv.mm"
include "eqtr4d.mm"
include "mireq.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"
include "tgbtwncom.mm"
include "mirbtwn.mm"
include "tgbtwnconn2.mm"
include "3jca.mm"
include "ishlg.mm"
include "mpbird.mm"

theorem mirhl2
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
  assume mirhl2.1: |- ( ph -> X =/= A )
  assume mirhl2.2: |- ( ph -> Y =/= A )
  assume mirhl2.3: |- ( ph -> A e. ( X I ( M ` Y ) ) )


  assert |- ( ph -> X ( K ` A ) Y )

  proof
    wph
    cX
    cY
    cA
    cK
    cfv
    wbr
    cX
    cA
    wne
    #
    cY
    cA
    wne
    #
    cX
    cA
    cY
    cI
    co
    wcel
    cY
    cA
    cX
    cI
    co
    wcel
    wo
    #
    w3a
    wph
    @0
    @1
    @2
    mirhl2.1
    mirhl2.2
    wph
    cY
    cM
    cfv
    #
    cA
    cX
    cY
    cP
    cG
    cI
    mirval.p
    mirval.i
    mirval.g
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
    #
    mirhl.a
    mirhl.x
    mirhl.y
    wph
    @1
    @3
    cA
    wne
    mirhl2.2
    wph
    @3
    cA
    cY
    cA
    wph
    @3
    cA
    wceq
    #
    cY
    cA
    wceq
    wph
    @5
    wa
    #
    cA
    cY
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
    @5
    mirval.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @5
    mirhl.a
    adantr
    #
    mirhl.m
    wph
    cY
    cP
    wcel
    @5
    mirhl.y
    adantr
    @8
    @6
    @3
    cA
    cA
    cM
    cfv
    wph
    @5
    simpr
    @6
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
    @7
    @8
    mirhl.m
    mircinv
    eqtr4d
    mireq
    ex
    necon3d
    mpd
    wph
    cX
    cA
    @3
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    mirhl.x
    mirhl.a
    @4
    mirhl2.3
    tgbtwncom
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
    mirhl.a
    mirhl.m
    mirhl.y
    mirbtwn
    tgbtwnconn2
    3jca
    wph
    cX
    cY
    cA
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
    mirhl.a
    mirval.g
    ishlg
    mpbird
end
