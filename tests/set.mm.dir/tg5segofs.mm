include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cop.mm"
include "wbr.mm"
include "w3a.mm"
include "brafs.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simpld.mm"
include "simprd.mm"
include "simp2d.mm"
include "simp3d.mm"
include "axtg5seg.mm"

theorem tg5segofs
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
  let c.mi: class .-
  let cO: class O
  assume tg5segofs.p: |- P = ( Base ` G )
  assume tg5segofs.m: |- .- = ( dist ` G )
  assume tg5segofs.s: |- I = ( Itv ` G )
  assume tg5segofs.g: |- ( ph -> G e. TarskiG )
  assume tg5segofs.a: |- ( ph -> A e. P )
  assume tg5segofs.b: |- ( ph -> B e. P )
  assume tg5segofs.c: |- ( ph -> C e. P )
  assume tg5segofs.d: |- ( ph -> D e. P )
  assume tg5segofs.e: |- ( ph -> E e. P )
  assume tg5segofs.f: |- ( ph -> F e. P )
  assume tg5segofs.o: |- O = ( AFS ` G )
  assume tg5segofs.h: |- ( ph -> H e. P )
  assume tg5segofs.i: |- ( ph -> I e. P )
  assume tg5segofs.1: |- ( ph -> <. <. A , B >. , <. C , D >. >. O <. <. E , F >. , <. H , I >. >. )
  assume tg5segofs.2: |- ( ph -> A =/= B )


  assert |- ( ph -> ( C .- D ) = ( H .- I ) )

  proof
    wph
    cE
    cF
    cH
    cP
    cD
    cG
    cI
    c.mi
    cI
    cA
    cB
    cC
    tg5segofs.p
    tg5segofs.m
    tg5segofs.s
    tg5segofs.g
    tg5segofs.a
    tg5segofs.b
    tg5segofs.c
    tg5segofs.e
    tg5segofs.f
    tg5segofs.h
    tg5segofs.d
    tg5segofs.i
    tg5segofs.2
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    #
    cF
    cE
    cH
    cI
    co
    wcel
    #
    wph
    @0
    @1
    wa
    #
    cA
    cB
    c.mi
    co
    cE
    cF
    c.mi
    co
    wceq
    #
    cB
    cC
    c.mi
    co
    cF
    cH
    c.mi
    co
    wceq
    #
    wa
    #
    cA
    cD
    c.mi
    co
    cE
    cI
    c.mi
    co
    wceq
    #
    cB
    cD
    c.mi
    co
    cF
    cI
    c.mi
    co
    wceq
    #
    wa
    #
    wph
    cA
    cB
    cop
    cC
    cD
    cop
    cop
    cE
    cF
    cop
    cH
    cI
    cop
    cop
    cO
    wbr
    @2
    @5
    @8
    w3a
    tg5segofs.1
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.mi
    cO
    cI
    cE
    cF
    cH
    tg5segofs.p
    tg5segofs.m
    tg5segofs.s
    tg5segofs.g
    tg5segofs.o
    tg5segofs.a
    tg5segofs.b
    tg5segofs.c
    tg5segofs.d
    tg5segofs.e
    tg5segofs.f
    tg5segofs.h
    tg5segofs.i
    brafs
    mpbid
    #
    simp1d
    #
    simpld
    wph
    @0
    @1
    @10
    simprd
    wph
    @3
    @4
    wph
    @2
    @5
    @8
    @9
    simp2d
    #
    simpld
    wph
    @3
    @4
    @11
    simprd
    wph
    @6
    @7
    wph
    @2
    @5
    @8
    @9
    simp3d
    #
    simpld
    wph
    @6
    @7
    @12
    simprd
    axtg5seg
end
