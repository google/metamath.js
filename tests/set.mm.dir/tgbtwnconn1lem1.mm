include "tgbtwnexch.mm"
include "tgbtwnexch3.mm"
include "tgbtwncom.mm"
include "co.mm"
include "axtgcgrrflx.mm"
include "eqtr2d.mm"
include "eqtr4d.mm"
include "tgcgrcomlr.mm"
include "tgcgrextend.mm"
include "tgcgrcomr.mm"
include "tgsegconeq.mm"

theorem tgbtwnconn1lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.mi: class .-
  assume tgbtwnconn1.p: |- P = ( Base ` G )
  assume tgbtwnconn1.i: |- I = ( Itv ` G )
  assume tgbtwnconn1.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnconn1.a: |- ( ph -> A e. P )
  assume tgbtwnconn1.b: |- ( ph -> B e. P )
  assume tgbtwnconn1.c: |- ( ph -> C e. P )
  assume tgbtwnconn1.d: |- ( ph -> D e. P )
  assume tgbtwnconn1.1: |- ( ph -> A =/= B )
  assume tgbtwnconn1.2: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnconn1.3: |- ( ph -> B e. ( A I D ) )
  assume tgbtwnconn1.m: |- .- = ( dist ` G )
  assume tgbtwnconn1.e: |- ( ph -> E e. P )
  assume tgbtwnconn1.f: |- ( ph -> F e. P )
  assume tgbtwnconn1.h: |- ( ph -> H e. P )
  assume tgbtwnconn1.j: |- ( ph -> J e. P )
  assume tgbtwnconn1.4: |- ( ph -> D e. ( A I E ) )
  assume tgbtwnconn1.5: |- ( ph -> C e. ( A I F ) )
  assume tgbtwnconn1.6: |- ( ph -> E e. ( A I H ) )
  assume tgbtwnconn1.7: |- ( ph -> F e. ( A I J ) )
  assume tgbtwnconn1.8: |- ( ph -> ( E .- D ) = ( C .- D ) )
  assume tgbtwnconn1.9: |- ( ph -> ( C .- F ) = ( C .- D ) )
  assume tgbtwnconn1.10: |- ( ph -> ( E .- H ) = ( B .- C ) )
  assume tgbtwnconn1.11: |- ( ph -> ( F .- J ) = ( B .- D ) )


  assert |- ( ph -> H = J )

  proof
    wph
    cB
    cJ
    cB
    cA
    cP
    cH
    cJ
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.b
    tgbtwnconn1.j
    tgbtwnconn1.b
    tgbtwnconn1.a
    tgbtwnconn1.h
    tgbtwnconn1.j
    tgbtwnconn1.1
    wph
    cA
    cB
    cE
    cH
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.e
    tgbtwnconn1.h
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.d
    tgbtwnconn1.e
    tgbtwnconn1.3
    tgbtwnconn1.4
    tgbtwnexch
    #
    tgbtwnconn1.6
    tgbtwnexch
    wph
    cA
    cB
    cF
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.f
    tgbtwnconn1.j
    wph
    cA
    cB
    cC
    cF
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.c
    tgbtwnconn1.f
    tgbtwnconn1.2
    tgbtwnconn1.5
    tgbtwnexch
    tgbtwnconn1.7
    tgbtwnexch
    wph
    cB
    cE
    cH
    cJ
    cP
    cC
    cB
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.b
    tgbtwnconn1.e
    tgbtwnconn1.h
    tgbtwnconn1.j
    tgbtwnconn1.c
    tgbtwnconn1.b
    wph
    cA
    cB
    cE
    cH
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.e
    tgbtwnconn1.h
    @0
    tgbtwnconn1.6
    tgbtwnexch3
    wph
    cB
    cC
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.b
    tgbtwnconn1.c
    tgbtwnconn1.j
    wph
    cA
    cB
    cC
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.c
    tgbtwnconn1.j
    tgbtwnconn1.2
    wph
    cA
    cC
    cF
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.c
    tgbtwnconn1.f
    tgbtwnconn1.j
    tgbtwnconn1.5
    tgbtwnconn1.7
    tgbtwnexch
    tgbtwnexch3
    tgbtwncom
    wph
    cB
    cD
    cE
    cJ
    cP
    cF
    cC
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.b
    tgbtwnconn1.d
    tgbtwnconn1.e
    tgbtwnconn1.j
    tgbtwnconn1.f
    tgbtwnconn1.c
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.b
    tgbtwnconn1.d
    tgbtwnconn1.e
    tgbtwnconn1.3
    tgbtwnconn1.4
    tgbtwnexch3
    wph
    cC
    cF
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.c
    tgbtwnconn1.f
    tgbtwnconn1.j
    wph
    cA
    cC
    cF
    cJ
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.a
    tgbtwnconn1.c
    tgbtwnconn1.f
    tgbtwnconn1.j
    tgbtwnconn1.5
    tgbtwnconn1.7
    tgbtwnexch3
    tgbtwncom
    wph
    cJ
    cF
    c.mi
    co
    cF
    cJ
    c.mi
    co
    cB
    cD
    c.mi
    co
    wph
    cP
    cG
    cI
    c.mi
    cJ
    cF
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.j
    tgbtwnconn1.f
    axtgcgrrflx
    tgbtwnconn1.11
    eqtr2d
    wph
    cE
    cD
    cC
    cF
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.e
    tgbtwnconn1.d
    tgbtwnconn1.c
    tgbtwnconn1.f
    wph
    cE
    cD
    c.mi
    co
    cC
    cD
    c.mi
    co
    cC
    cF
    c.mi
    co
    tgbtwnconn1.8
    tgbtwnconn1.9
    eqtr4d
    tgcgrcomlr
    tgcgrextend
    wph
    cE
    cH
    cB
    cC
    cP
    cG
    cI
    c.mi
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.e
    tgbtwnconn1.h
    tgbtwnconn1.b
    tgbtwnconn1.c
    tgbtwnconn1.10
    tgcgrcomr
    tgcgrextend
    wph
    cP
    cG
    cI
    c.mi
    cB
    cJ
    tgbtwnconn1.p
    tgbtwnconn1.m
    tgbtwnconn1.i
    tgbtwnconn1.g
    tgbtwnconn1.b
    tgbtwnconn1.j
    axtgcgrrflx
    tgsegconeq
end
