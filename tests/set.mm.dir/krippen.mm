include "co.mm"
include "cleg.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "wceq.mm"
include "eqid.mm"
include "simpr.mm"
include "krippenlem.mm"
include "tgbtwncom.mm"
include "legtrid.mm"
include "mpjaodan.mm"

theorem krippen
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume krippen.m: |- M = ( S ` X )
  assume krippen.n: |- N = ( S ` Y )
  assume krippen.a: |- ( ph -> A e. P )
  assume krippen.b: |- ( ph -> B e. P )
  assume krippen.c: |- ( ph -> C e. P )
  assume krippen.e: |- ( ph -> E e. P )
  assume krippen.f: |- ( ph -> F e. P )
  assume krippen.x: |- ( ph -> X e. P )
  assume krippen.y: |- ( ph -> Y e. P )
  assume krippen.1: |- ( ph -> C e. ( A I E ) )
  assume krippen.2: |- ( ph -> C e. ( B I F ) )
  assume krippen.3: |- ( ph -> ( C .- A ) = ( C .- B ) )
  assume krippen.4: |- ( ph -> ( C .- E ) = ( C .- F ) )
  assume krippen.5: |- ( ph -> B = ( M ` A ) )
  assume krippen.6: |- ( ph -> F = ( N ` E ) )


  assert |- ( ph -> C e. ( X I Y ) )

  proof
    wph
    cC
    cA
    c.mi
    co
    #
    cC
    cE
    c.mi
    co
    #
    cG
    cleg
    cfv
    #
    wbr
    #
    cC
    cX
    cY
    cI
    co
    wcel
    @1
    @0
    @2
    wbr
    #
    wph
    @3
    wa
    cA
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cI
    cL
    @2
    cM
    c.mi
    cN
    cX
    cY
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
    @3
    mirval.g
    adantr
    krippen.m
    krippen.n
    wph
    cA
    cP
    wcel
    #
    @3
    krippen.a
    adantr
    wph
    cB
    cP
    wcel
    #
    @3
    krippen.b
    adantr
    wph
    cC
    cP
    wcel
    #
    @3
    krippen.c
    adantr
    wph
    cE
    cP
    wcel
    #
    @3
    krippen.e
    adantr
    wph
    cF
    cP
    wcel
    #
    @3
    krippen.f
    adantr
    wph
    cX
    cP
    wcel
    #
    @3
    krippen.x
    adantr
    wph
    cY
    cP
    wcel
    #
    @3
    krippen.y
    adantr
    wph
    cC
    cA
    cE
    cI
    co
    wcel
    #
    @3
    krippen.1
    adantr
    wph
    cC
    cB
    cF
    cI
    co
    wcel
    #
    @3
    krippen.2
    adantr
    wph
    @0
    cC
    cB
    c.mi
    co
    wceq
    #
    @3
    krippen.3
    adantr
    wph
    @1
    cC
    cF
    c.mi
    co
    wceq
    #
    @3
    krippen.4
    adantr
    wph
    cB
    cA
    cM
    cfv
    wceq
    #
    @3
    krippen.5
    adantr
    wph
    cF
    cE
    cN
    cfv
    wceq
    #
    @3
    krippen.6
    adantr
    @2
    eqid
    #
    wph
    @3
    simpr
    krippenlem
    wph
    @4
    wa
    #
    cY
    cC
    cX
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
    mirval.g
    adantr
    #
    wph
    @12
    @4
    krippen.y
    adantr
    #
    wph
    @8
    @4
    krippen.c
    adantr
    #
    wph
    @11
    @4
    krippen.x
    adantr
    #
    @20
    cE
    cF
    cC
    cP
    cS
    cA
    cB
    cG
    cI
    cL
    @2
    cN
    c.mi
    cM
    cY
    cX
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    @21
    krippen.n
    krippen.m
    wph
    @9
    @4
    krippen.e
    adantr
    #
    wph
    @10
    @4
    krippen.f
    adantr
    #
    @23
    wph
    @6
    @4
    krippen.a
    adantr
    #
    wph
    @7
    @4
    krippen.b
    adantr
    #
    @22
    @24
    @20
    cA
    cC
    cE
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @21
    @27
    @23
    @25
    wph
    @13
    @4
    krippen.1
    adantr
    tgbtwncom
    @20
    cB
    cC
    cF
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @21
    @28
    @23
    @26
    wph
    @14
    @4
    krippen.2
    adantr
    tgbtwncom
    wph
    @16
    @4
    krippen.4
    adantr
    wph
    @15
    @4
    krippen.3
    adantr
    wph
    @18
    @4
    krippen.6
    adantr
    wph
    @17
    @4
    krippen.5
    adantr
    @19
    wph
    @4
    simpr
    krippenlem
    tgbtwncom
    wph
    cC
    cA
    cC
    cE
    cP
    cG
    cI
    @2
    c.mi
    mirval.p
    mirval.d
    mirval.i
    @19
    mirval.g
    krippen.c
    krippen.a
    krippen.c
    krippen.e
    legtrid
    mpjaodan
end
