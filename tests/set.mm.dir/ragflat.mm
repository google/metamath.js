include "wceq.mm"
include "simpr.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "eqid.mm"
include "mircl.mm"
include "cs3.mm"
include "crag.mm"
include "co.mm"
include "mircgr.mm"
include "tgcgrcomlr.mm"
include "israg.mm"
include "mpbid.mm"
include "ragcom.mm"
include "mirbtwn.mm"
include "tgbtwncom.mm"
include "btwncolg1.mm"
include "ragcol.mm"
include "3eqtrd.mm"
include "mpbird.mm"
include "ragflat2.mm"
include "pm2.61dane.mm"

theorem ragflat
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vg: setvar g
  let vw: setvar w
  assume israg.p: |- P = ( Base ` G )
  assume israg.d: |- .- = ( dist ` G )
  assume israg.i: |- I = ( Itv ` G )
  assume israg.l: |- L = ( LineG ` G )
  assume israg.s: |- S = ( pInvG ` G )
  assume israg.g: |- ( ph -> G e. TarskiG )
  assume israg.a: |- ( ph -> A e. P )
  assume israg.b: |- ( ph -> B e. P )
  assume israg.c: |- ( ph -> C e. P )
  assume ragflat.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume ragflat.2: |- ( ph -> <" A C B "> e. ( raG ` G ) )


  assert |- ( ph -> B = C )

  proof
    wph
    cB
    cC
    wceq
    #
    cB
    cC
    wph
    @0
    simpr
    wph
    cB
    cC
    wne
    #
    wa
    #
    cA
    cB
    cC
    cA
    cC
    cS
    cfv
    #
    cfv
    #
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    wph
    cG
    cstrkg
    wcel
    @1
    israg.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @1
    israg.a
    adantr
    #
    wph
    cB
    cP
    wcel
    @1
    israg.b
    adantr
    #
    wph
    cC
    cP
    wcel
    @1
    israg.c
    adantr
    #
    @2
    cC
    cP
    cS
    cG
    cI
    cL
    @3
    c.mi
    cA
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @8
    @3
    eqid
    #
    @6
    mircl
    #
    wph
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    #
    wcel
    #
    @1
    ragflat.1
    adantr
    #
    @2
    @4
    cB
    cC
    cs3
    @11
    wcel
    @4
    cC
    c.mi
    co
    #
    @4
    cC
    cB
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    #
    wceq
    @2
    @14
    cA
    cC
    c.mi
    co
    #
    cA
    @16
    c.mi
    co
    #
    @17
    @2
    cC
    @4
    cC
    cA
    cP
    cG
    cI
    c.mi
    israg.p
    israg.d
    israg.i
    @5
    @8
    @10
    @8
    @6
    @2
    cC
    cA
    cP
    cS
    cG
    cI
    cL
    @3
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @8
    @9
    @6
    mircgr
    tgcgrcomlr
    @2
    @12
    @18
    @19
    wceq
    @13
    @2
    cA
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @6
    @7
    @8
    israg
    mpbid
    @2
    @16
    cA
    @16
    @4
    cP
    cG
    cI
    c.mi
    israg.p
    israg.d
    israg.i
    @5
    @2
    cB
    cP
    cS
    cG
    cI
    cL
    @15
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @7
    @15
    eqid
    #
    @8
    mircl
    #
    @6
    @21
    @10
    @2
    @16
    cC
    cA
    cs3
    @11
    wcel
    @16
    cA
    c.mi
    co
    @16
    @4
    c.mi
    co
    wceq
    @2
    cB
    cC
    cA
    @16
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @7
    @8
    @6
    @21
    @2
    cA
    cC
    cB
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @6
    @8
    @7
    wph
    cA
    cC
    cB
    cs3
    @11
    wcel
    @1
    ragflat.2
    adantr
    ragcom
    wph
    @1
    simpr
    @2
    cP
    cG
    cI
    cL
    cC
    @16
    cB
    israg.p
    israg.l
    israg.i
    @5
    @8
    @21
    @7
    @2
    @16
    cB
    cC
    cP
    cG
    cI
    c.mi
    israg.p
    israg.d
    israg.i
    @5
    @21
    @7
    @8
    @2
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    @15
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @7
    @20
    @8
    mirbtwn
    tgbtwncom
    btwncolg1
    ragcol
    @2
    @16
    cC
    cA
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @21
    @8
    @6
    israg
    mpbid
    tgcgrcomlr
    3eqtrd
    @2
    @4
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @10
    @7
    @8
    israg
    mpbird
    @2
    @4
    cC
    cA
    cP
    cG
    cI
    c.mi
    israg.p
    israg.d
    israg.i
    @5
    @10
    @8
    @6
    @2
    cC
    cA
    cP
    cS
    cG
    cI
    cL
    @3
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    @5
    @8
    @9
    @6
    mirbtwn
    tgbtwncom
    ragflat2
    pm2.61dane
end
