include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "chlg.mm"
include "w3a.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "simpllr.mm"
include "ad3antrrr.mm"
include "cstrkg.mm"
include "simpr2.mm"
include "simplr.mm"
include "simpr3.mm"
include "simpr1.mm"
include "tgbtwnxfr.mm"
include "tgbtwncom.mm"
include "btwnhl.mm"
include "ccgra.mm"
include "wrex.mm"
include "iscgra.mm"
include "mpbid.mm"
include "r19.29vva.mm"

theorem cgrabtwn
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
  assume cgrabtwn.2: |- ( ph -> B e. ( A I C ) )


  assert |- ( ph -> E e. ( D I F ) )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    vx
    cv
    #
    cE
    vy
    cv
    #
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @1
    cD
    cE
    cG
    chlg
    cfv
    #
    cfv
    #
    wbr
    #
    @2
    cF
    @6
    wbr
    #
    w3a
    #
    cE
    cD
    cF
    cI
    co
    wcel
    vx
    vy
    cP
    cP
    wph
    @1
    cP
    wcel
    #
    wa
    #
    @2
    cP
    wcel
    #
    wa
    #
    @9
    wa
    #
    @1
    cD
    cF
    cE
    cP
    cG
    cI
    @5
    cgracol.p
    cgracol.i
    @5
    eqid
    #
    wph
    @10
    @12
    @9
    simpllr
    #
    wph
    cD
    cP
    wcel
    @10
    @12
    @9
    cgracol.d
    ad3antrrr
    wph
    cF
    cP
    wcel
    @10
    @12
    @9
    cgracol.f
    ad3antrrr
    #
    wph
    cG
    cstrkg
    wcel
    @10
    @12
    @9
    cgracol.g
    ad3antrrr
    #
    wph
    cE
    cP
    wcel
    @10
    @12
    @9
    cgracol.e
    ad3antrrr
    #
    @13
    @4
    @7
    @8
    simpr2
    @14
    cF
    cE
    @1
    cP
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @18
    @17
    @19
    @16
    @14
    @2
    cF
    @1
    cE
    cP
    cG
    cI
    @5
    cgracol.p
    cgracol.i
    @15
    @11
    @12
    @9
    simplr
    #
    @17
    @16
    @18
    @19
    @13
    @4
    @7
    @8
    simpr3
    @14
    @1
    cE
    @2
    cP
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @18
    @16
    @19
    @20
    @14
    cA
    cB
    cC
    @1
    cP
    @3
    cE
    @2
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @3
    eqid
    @18
    wph
    cA
    cP
    wcel
    @10
    @12
    @9
    cgracol.a
    ad3antrrr
    wph
    cB
    cP
    wcel
    @10
    @12
    @9
    cgracol.b
    ad3antrrr
    wph
    cC
    cP
    wcel
    @10
    @12
    @9
    cgracol.c
    ad3antrrr
    @16
    @19
    @20
    @13
    @4
    @7
    @8
    simpr1
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    @10
    @12
    @9
    cgrabtwn.2
    ad3antrrr
    tgbtwnxfr
    tgbtwncom
    btwnhl
    tgbtwncom
    btwnhl
    wph
    @0
    cD
    cE
    cF
    cs3
    cG
    ccgra
    cfv
    wbr
    @9
    vy
    cP
    wrex
    vx
    cP
    wrex
    cgracol.1
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    @5
    cgracol.p
    cgracol.i
    @15
    cgracol.g
    cgracol.a
    cgracol.b
    cgracol.c
    cgracol.d
    cgracol.e
    cgracol.f
    iscgra
    mpbid
    r19.29vva
end
