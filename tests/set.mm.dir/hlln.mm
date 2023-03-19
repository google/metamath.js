include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgbtwncom.mm"
include "3mix1d.mm"
include "3mix2d.mm"
include "wne.mm"
include "wo.mm"
include "wbr.mm"
include "w3a.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp3d.mm"
include "mpjaodan.mm"
include "simp2d.mm"
include "tgellng.mm"
include "mpbird.mm"

theorem hlln
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume hlln.l: |- L = ( LineG ` G )
  assume hlln.2: |- ( ph -> A ( K ` C ) B )


  assert |- ( ph -> A e. ( B L C ) )

  proof
    wph
    cA
    cB
    cC
    cL
    co
    wcel
    cA
    cB
    cC
    cI
    co
    wcel
    #
    cB
    cA
    cC
    cI
    co
    wcel
    #
    cC
    cB
    cA
    cI
    co
    wcel
    #
    w3o
    #
    wph
    cA
    cC
    cB
    cI
    co
    wcel
    #
    @3
    cB
    cC
    cA
    cI
    co
    wcel
    #
    wph
    @4
    wa
    #
    @0
    @1
    @2
    @6
    cC
    cA
    cB
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @7
    eqid
    #
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    #
    @4
    hlln.1
    adantr
    wph
    cC
    cP
    wcel
    #
    @4
    ishlg.c
    adantr
    wph
    cA
    cP
    wcel
    #
    @4
    ishlg.a
    adantr
    wph
    cB
    cP
    wcel
    #
    @4
    ishlg.b
    adantr
    wph
    @4
    simpr
    tgbtwncom
    3mix1d
    wph
    @5
    wa
    #
    @1
    @0
    @2
    @13
    cC
    cB
    cA
    cP
    cG
    cI
    @7
    ishlg.p
    @8
    ishlg.i
    wph
    @9
    @5
    hlln.1
    adantr
    wph
    @10
    @5
    ishlg.c
    adantr
    wph
    @12
    @5
    ishlg.b
    adantr
    wph
    @11
    @5
    ishlg.a
    adantr
    wph
    @5
    simpr
    tgbtwncom
    3mix2d
    wph
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    @4
    @5
    wo
    #
    wph
    cA
    cB
    cC
    cK
    cfv
    wbr
    @14
    @15
    @16
    w3a
    hlln.2
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.b
    ishlg.c
    hlln.1
    ishlg
    mpbid
    #
    simp3d
    mpjaodan
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    ishlg.p
    hlln.l
    ishlg.i
    hlln.1
    ishlg.b
    ishlg.c
    wph
    @14
    @15
    @16
    @17
    simp2d
    ishlg.a
    tgellng
    mpbird
end
