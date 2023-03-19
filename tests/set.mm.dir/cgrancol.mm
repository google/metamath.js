include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "cs3.mm"
include "ccgra.mm"
include "wbr.mm"
include "cgracom.mm"
include "simpr.mm"
include "cgracol.mm"
include "wn.mm"
include "pm2.65da.mm"

theorem cgrancol
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
  let cL: class L
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  assume cgracol.p: |- P = ( Base ` G )
  assume cgracol.i: |- I = ( Itv ` G )
  assume cgracol.m: |- .- = ( dist ` G )
  assume cgracol.g: |- ( ph -> G e. TarskiG )
  assume cgracol.a: |- ( ph -> A e. P )
  assume cgracol.b: |- ( ph -> B e. P )
  assume cgracol.c: |- ( ph -> C e. P )
  assume cgracol.d: |- ( ph -> D e. P )
  assume cgracol.e: |- ( ph -> E e. P )
  assume cgracol.f: |- ( ph -> F e. P )
  assume cgracol.1: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
  assume cgrancol.l: |- L = ( LineG ` G )
  assume cgrancol.2: |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) )


  assert |- ( ph -> -. ( F e. ( D L E ) \/ D = E ) )

  proof
    wph
    cF
    cD
    cE
    cL
    co
    wcel
    cD
    cE
    wceq
    wo
    #
    cC
    cA
    cB
    cL
    co
    wcel
    cA
    cB
    wceq
    wo
    #
    wph
    @0
    wa
    #
    cD
    cE
    cF
    cA
    cP
    cB
    cC
    cG
    cI
    cL
    c.mi
    cgracol.p
    cgracol.i
    cgracol.m
    wph
    cG
    cstrkg
    wcel
    @0
    cgracol.g
    adantr
    #
    wph
    cD
    cP
    wcel
    @0
    cgracol.d
    adantr
    #
    wph
    cE
    cP
    wcel
    @0
    cgracol.e
    adantr
    #
    wph
    cF
    cP
    wcel
    @0
    cgracol.f
    adantr
    #
    wph
    cA
    cP
    wcel
    @0
    cgracol.a
    adantr
    #
    wph
    cB
    cP
    wcel
    @0
    cgracol.b
    adantr
    #
    wph
    cC
    cP
    wcel
    @0
    cgracol.c
    adantr
    #
    @2
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    cG
    chlg
    cfv
    #
    cgracol.p
    cgracol.i
    @3
    @10
    eqid
    @7
    @8
    @9
    @4
    @5
    @6
    wph
    cA
    cB
    cC
    cs3
    cD
    cE
    cF
    cs3
    cG
    ccgra
    cfv
    wbr
    @0
    cgracol.1
    adantr
    cgracom
    cgrancol.l
    wph
    @0
    simpr
    cgracol
    wph
    @1
    wn
    @0
    cgrancol.2
    adantr
    pm2.65da
end
