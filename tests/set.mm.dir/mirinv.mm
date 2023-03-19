include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "co.mm"
include "mirbtwn.mm"
include "simpr.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "axtgbtwnid.mm"
include "eqcomd.mm"
include "eqidd.mm"
include "tgbtwntriv1.mm"
include "eqeltrd.mm"
include "ismir.mm"
include "impbida.mm"

theorem mirinv
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
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume mirinv.b: |- ( ph -> B e. P )


  assert |- ( ph -> ( ( M ` B ) = B <-> A = B ) )

  proof
    wph
    cB
    cM
    cfv
    #
    cB
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    @1
    wa
    #
    cB
    cA
    @3
    cP
    cG
    cI
    c.mi
    cB
    cA
    mirval.p
    mirval.d
    mirval.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    mirval.g
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @1
    mirinv.b
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @1
    mirval.a
    adantr
    #
    @3
    cA
    @0
    cB
    cI
    co
    cB
    cB
    cI
    co
    #
    @3
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
    @5
    @9
    mirfv.m
    @7
    mirbtwn
    @3
    @0
    cB
    cB
    cI
    wph
    @1
    simpr
    oveq1d
    eleqtrd
    axtgbtwnid
    eqcomd
    wph
    @2
    wa
    #
    cB
    @0
    @11
    cA
    cB
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
    @4
    @2
    mirval.g
    adantr
    #
    wph
    @8
    @2
    mirval.a
    adantr
    mirfv.m
    wph
    @6
    @2
    mirinv.b
    adantr
    #
    @13
    @11
    cA
    cB
    c.mi
    co
    eqidd
    @11
    cA
    cB
    @10
    wph
    @2
    simpr
    @11
    cB
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @12
    @13
    @13
    tgbtwntriv1
    eqeltrd
    ismir
    eqcomd
    impbida
end
