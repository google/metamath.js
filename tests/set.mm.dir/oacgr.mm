include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "necomd.mm"
include "cgraswap.mm"
include "tgbtwncom.mm"
include "sacgr.mm"
include "cgratr.mm"

theorem oacgr
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
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cL: class L
  assume dfcgra2.p: |- P = ( Base ` G )
  assume dfcgra2.i: |- I = ( Itv ` G )
  assume dfcgra2.m: |- .- = ( dist ` G )
  assume dfcgra2.g: |- ( ph -> G e. TarskiG )
  assume dfcgra2.a: |- ( ph -> A e. P )
  assume dfcgra2.b: |- ( ph -> B e. P )
  assume dfcgra2.c: |- ( ph -> C e. P )
  assume dfcgra2.d: |- ( ph -> D e. P )
  assume dfcgra2.e: |- ( ph -> E e. P )
  assume dfcgra2.f: |- ( ph -> F e. P )
  assume oacgr.1: |- ( ph -> B e. ( A I D ) )
  assume oacgr.2: |- ( ph -> B e. ( C I F ) )
  assume oacgr.3: |- ( ph -> B =/= A )
  assume oacgr.4: |- ( ph -> B =/= C )
  assume oacgr.5: |- ( ph -> B =/= D )
  assume oacgr.6: |- ( ph -> B =/= F )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" D B F "> )

  proof
    wph
    cA
    cB
    cC
    cC
    cP
    cB
    cB
    cA
    cG
    cD
    cI
    cF
    cG
    chlg
    cfv
    #
    dfcgra2.p
    dfcgra2.i
    dfcgra2.g
    @0
    eqid
    #
    dfcgra2.a
    dfcgra2.b
    dfcgra2.c
    dfcgra2.c
    dfcgra2.b
    dfcgra2.a
    wph
    cA
    cB
    cC
    cP
    cG
    cI
    @0
    dfcgra2.p
    dfcgra2.i
    dfcgra2.g
    @1
    dfcgra2.a
    dfcgra2.b
    dfcgra2.c
    wph
    cB
    cA
    oacgr.3
    necomd
    oacgr.4
    cgraswap
    dfcgra2.d
    dfcgra2.b
    dfcgra2.f
    wph
    cF
    cB
    cA
    cA
    cP
    cB
    cF
    cG
    cI
    c.mi
    cC
    cD
    dfcgra2.p
    dfcgra2.i
    dfcgra2.m
    dfcgra2.g
    dfcgra2.f
    dfcgra2.b
    dfcgra2.a
    dfcgra2.a
    dfcgra2.b
    dfcgra2.f
    dfcgra2.c
    dfcgra2.d
    wph
    cF
    cB
    cA
    cP
    cG
    cI
    @0
    dfcgra2.p
    dfcgra2.i
    dfcgra2.g
    @1
    dfcgra2.f
    dfcgra2.b
    dfcgra2.a
    wph
    cB
    cF
    oacgr.6
    necomd
    oacgr.3
    cgraswap
    wph
    cC
    cB
    cF
    cP
    cG
    cI
    c.mi
    dfcgra2.p
    dfcgra2.m
    dfcgra2.i
    dfcgra2.g
    dfcgra2.c
    dfcgra2.b
    dfcgra2.f
    oacgr.2
    tgbtwncom
    oacgr.1
    oacgr.4
    oacgr.5
    sacgr
    cgratr
end
