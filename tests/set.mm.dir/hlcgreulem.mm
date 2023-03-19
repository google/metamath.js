include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprr.mm"
include "necomd.mm"
include "cfv.mm"
include "wbr.mm"
include "hlcomd.mm"
include "simprl.mm"
include "btwnhl.mm"
include "tgbtwncom.mm"
include "tgsegconeq.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "nehash2.mm"
include "tgbtwndiff.mm"
include "r19.29a.mm"

theorem hlcgreulem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vx: setvar x
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume hlcgrex.m: |- .- = ( dist ` G )
  assume hlcgrex.1: |- ( ph -> D =/= A )
  assume hlcgrex.2: |- ( ph -> B =/= C )
  assume hlcgreulem.x: |- ( ph -> X e. P )
  assume hlcgreulem.y: |- ( ph -> Y e. P )
  assume hlcgreulem.1: |- ( ph -> X ( K ` A ) D )
  assume hlcgreulem.2: |- ( ph -> Y ( K ` A ) D )
  assume hlcgreulem.3: |- ( ph -> ( A .- X ) = ( B .- C ) )
  assume hlcgreulem.4: |- ( ph -> ( A .- Y ) = ( B .- C ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    cA
    cD
    vy
    cv
    #
    cI
    co
    wcel
    #
    cA
    @0
    wne
    #
    wa
    #
    cX
    cY
    wceq
    vy
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @3
    wa
    #
    cA
    cB
    cC
    @0
    cP
    cX
    cY
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    @4
    @3
    hlln.1
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    @4
    @3
    ishlg.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    @4
    @3
    ishlg.b
    ad2antrr
    wph
    cC
    cP
    wcel
    @4
    @3
    ishlg.c
    ad2antrr
    wph
    @4
    @3
    simplr
    #
    wph
    cX
    cP
    wcel
    @4
    @3
    hlcgreulem.x
    ad2antrr
    #
    wph
    cY
    cP
    wcel
    @4
    @3
    hlcgreulem.y
    ad2antrr
    #
    @6
    cA
    @0
    @5
    @1
    @2
    simprr
    necomd
    @6
    cX
    cA
    @0
    cP
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    @7
    @10
    @8
    @9
    @6
    cD
    cX
    @0
    cA
    cP
    cG
    cI
    cK
    ishlg.p
    ishlg.i
    ishlg.k
    wph
    cD
    cP
    wcel
    @4
    @3
    hltr.d
    ad2antrr
    #
    @10
    @9
    @7
    @8
    wph
    cD
    cX
    cA
    cK
    cfv
    #
    wbr
    @4
    @3
    wph
    cX
    cD
    cA
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    hlcgreulem.x
    hltr.d
    ishlg.a
    hlln.1
    hlcgreulem.1
    hlcomd
    ad2antrr
    @5
    @1
    @2
    simprl
    #
    btwnhl
    tgbtwncom
    @6
    cY
    cA
    @0
    cP
    cG
    cI
    c.mi
    ishlg.p
    hlcgrex.m
    ishlg.i
    @7
    @11
    @8
    @9
    @6
    cD
    cY
    @0
    cA
    cP
    cG
    cI
    cK
    ishlg.p
    ishlg.i
    ishlg.k
    @12
    @11
    @9
    @7
    @8
    wph
    cD
    cY
    @13
    wbr
    @4
    @3
    wph
    cY
    cD
    cA
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    hlcgreulem.y
    hltr.d
    ishlg.a
    hlln.1
    hlcgreulem.2
    hlcomd
    ad2antrr
    @14
    btwnhl
    tgbtwncom
    wph
    cA
    cX
    c.mi
    co
    cB
    cC
    c.mi
    co
    #
    wceq
    @4
    @3
    hlcgreulem.3
    ad2antrr
    wph
    cA
    cY
    c.mi
    co
    @15
    wceq
    @4
    @3
    hlcgreulem.4
    ad2antrr
    tgsegconeq
    wph
    cD
    cA
    cP
    cG
    cI
    c.mi
    vy
    ishlg.p
    hlcgrex.m
    ishlg.i
    hlln.1
    hltr.d
    ishlg.a
    wph
    cB
    cC
    cP
    cvv
    cP
    cvv
    wcel
    wph
    cP
    cG
    cbs
    cfv
    cvv
    ishlg.p
    cG
    cbs
    fvex
    eqeltri
    a1i
    ishlg.b
    ishlg.c
    hlcgrex.2
    nehash2
    tgbtwndiff
    r19.29a
end
