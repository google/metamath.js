include "co.mm"
include "cmid.mm"
include "cfv.mm"
include "cmir.mm"
include "clng.mm"
include "clmi.mm"
include "eqid.mm"
include "midcl.mm"
include "mircl.mm"
include "mirrag.mm"
include "miriso.mm"
include "eqtr4d.mm"
include "wceq.mm"
include "midcom.mm"
include "ismidb.mm"
include "mpbird.mm"
include "hypcgrlem2.mm"
include "eqtrd.mm"

theorem hypcgr
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
  assume hypcgr.p: |- P = ( Base ` G )
  assume hypcgr.m: |- .- = ( dist ` G )
  assume hypcgr.i: |- I = ( Itv ` G )
  assume hypcgr.g: |- ( ph -> G e. TarskiG )
  assume hypcgr.h: |- ( ph -> G TarskiGDim>= 2 )
  assume hypcgr.a: |- ( ph -> A e. P )
  assume hypcgr.b: |- ( ph -> B e. P )
  assume hypcgr.c: |- ( ph -> C e. P )
  assume hypcgr.d: |- ( ph -> D e. P )
  assume hypcgr.e: |- ( ph -> E e. P )
  assume hypcgr.f: |- ( ph -> F e. P )
  assume hypcgr.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume hypcgr.2: |- ( ph -> <" D E F "> e. ( raG ` G ) )
  assume hypcgr.3: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume hypcgr.4: |- ( ph -> ( B .- C ) = ( E .- F ) )


  assert |- ( ph -> ( A .- C ) = ( D .- F ) )

  proof
    wph
    cA
    cC
    c.mi
    co
    cD
    cB
    cE
    cG
    cmid
    cfv
    #
    co
    #
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    cF
    @3
    cfv
    #
    c.mi
    co
    cD
    cF
    c.mi
    co
    wph
    cA
    cB
    cC
    @4
    cP
    cC
    @5
    @0
    co
    cB
    cG
    clng
    cfv
    #
    co
    cG
    clmi
    cfv
    cfv
    #
    cE
    @3
    cfv
    #
    @5
    cG
    cI
    c.mi
    hypcgr.p
    hypcgr.m
    hypcgr.i
    hypcgr.g
    hypcgr.h
    hypcgr.a
    hypcgr.b
    hypcgr.c
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cD
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @6
    eqid
    #
    @2
    eqid
    #
    hypcgr.g
    wph
    cB
    cE
    cP
    cG
    cI
    c.mi
    hypcgr.p
    hypcgr.m
    hypcgr.i
    hypcgr.g
    hypcgr.h
    hypcgr.b
    hypcgr.e
    midcl
    #
    @3
    eqid
    #
    hypcgr.d
    mircl
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cE
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    @11
    @12
    hypcgr.e
    mircl
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cF
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    @11
    @12
    hypcgr.f
    mircl
    hypcgr.1
    wph
    cD
    cE
    cF
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    hypcgr.d
    hypcgr.e
    hypcgr.f
    hypcgr.2
    @12
    @11
    mirrag
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    @4
    @8
    c.mi
    co
    hypcgr.3
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cD
    cE
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    @11
    @12
    hypcgr.d
    hypcgr.e
    miriso
    eqtr4d
    wph
    cB
    cC
    c.mi
    co
    cE
    cF
    c.mi
    co
    @8
    @5
    c.mi
    co
    hypcgr.4
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cE
    cF
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    @11
    @12
    hypcgr.e
    hypcgr.f
    miriso
    eqtr4d
    wph
    cB
    @8
    wceq
    cE
    cB
    @0
    co
    @1
    wceq
    wph
    cE
    cB
    cP
    cG
    cI
    c.mi
    hypcgr.p
    hypcgr.m
    hypcgr.i
    hypcgr.g
    hypcgr.h
    hypcgr.e
    hypcgr.b
    midcom
    wph
    cE
    cB
    cP
    @2
    cG
    cI
    @1
    c.mi
    hypcgr.p
    hypcgr.m
    hypcgr.i
    hypcgr.g
    hypcgr.h
    hypcgr.e
    hypcgr.b
    @10
    @11
    ismidb
    mpbird
    @7
    eqid
    hypcgrlem2
    wph
    @1
    cP
    @2
    cG
    cI
    @6
    @3
    c.mi
    cD
    cF
    hypcgr.p
    hypcgr.m
    hypcgr.i
    @9
    @10
    hypcgr.g
    @11
    @12
    hypcgr.d
    hypcgr.f
    miriso
    eqtrd
end
