include "co.mm"
include "wceq.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "cstrkg.mm"
include "wcel.mm"
include "tgcgreq.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "tgcgrtriv.mm"
include "tgcgrcomlr.mm"
include "axtg5seg.mm"
include "pm2.61dane.mm"

theorem tgcgrextend
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgcgrextend.a: |- ( ph -> A e. P )
  assume tgcgrextend.b: |- ( ph -> B e. P )
  assume tgcgrextend.c: |- ( ph -> C e. P )
  assume tgcgrextend.d: |- ( ph -> D e. P )
  assume tgcgrextend.e: |- ( ph -> E e. P )
  assume tgcgrextend.f: |- ( ph -> F e. P )
  assume tgcgrextend.1: |- ( ph -> B e. ( A I C ) )
  assume tgcgrextend.2: |- ( ph -> E e. ( D I F ) )
  assume tgcgrextend.3: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume tgcgrextend.4: |- ( ph -> ( B .- C ) = ( E .- F ) )


  assert |- ( ph -> ( A .- C ) = ( D .- F ) )

  proof
    wph
    cA
    cC
    c.mi
    co
    #
    cD
    cF
    c.mi
    co
    #
    wceq
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    wa
    #
    cB
    cC
    c.mi
    co
    #
    cE
    cF
    c.mi
    co
    #
    @0
    @1
    wph
    @4
    @5
    wceq
    #
    @2
    tgcgrextend.4
    adantr
    @3
    cA
    cB
    cC
    c.mi
    wph
    @2
    simpr
    #
    oveq1d
    @3
    cD
    cE
    cF
    c.mi
    @3
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    cG
    cstrkg
    wcel
    #
    @2
    tkgeom.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @2
    tgcgrextend.a
    adantr
    wph
    cB
    cP
    wcel
    #
    @2
    tgcgrextend.b
    adantr
    wph
    cD
    cP
    wcel
    #
    @2
    tgcgrextend.d
    adantr
    wph
    cE
    cP
    wcel
    #
    @2
    tgcgrextend.e
    adantr
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    wceq
    #
    @2
    tgcgrextend.3
    adantr
    @7
    tgcgreq
    oveq1d
    3eqtr4d
    wph
    cA
    cB
    wne
    #
    wa
    #
    cC
    cA
    cF
    cD
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    wph
    @8
    @14
    tkgeom.g
    adantr
    #
    wph
    cC
    cP
    wcel
    @14
    tgcgrextend.c
    adantr
    #
    wph
    @9
    @14
    tgcgrextend.a
    adantr
    #
    wph
    cF
    cP
    wcel
    @14
    tgcgrextend.f
    adantr
    #
    wph
    @11
    @14
    tgcgrextend.d
    adantr
    #
    @15
    cD
    cE
    cF
    cP
    cA
    cG
    cI
    c.mi
    cD
    cA
    cB
    cC
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @16
    @18
    wph
    @10
    @14
    tgcgrextend.b
    adantr
    #
    @17
    @20
    wph
    @12
    @14
    tgcgrextend.e
    adantr
    #
    @19
    @18
    @20
    wph
    @14
    simpr
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    @14
    tgcgrextend.1
    adantr
    wph
    cE
    cD
    cF
    cI
    co
    wcel
    @14
    tgcgrextend.2
    adantr
    wph
    @13
    @14
    tgcgrextend.3
    adantr
    #
    wph
    @6
    @14
    tgcgrextend.4
    adantr
    @15
    cA
    cD
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @16
    @18
    @20
    tgcgrtriv
    @15
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    @16
    @18
    @21
    @20
    @22
    @23
    tgcgrcomlr
    axtg5seg
    tgcgrcomlr
    pm2.61dane
end
