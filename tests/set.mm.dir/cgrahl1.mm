include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "ccgra.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "simpr1.mm"
include "simpr2.mm"
include "hlcomd.mm"
include "hltr.mm"
include "simpr3.mm"
include "iscgrad.mm"
include "wrex.mm"
include "iscgra.mm"
include "mpbid.mm"
include "r19.29vva.mm"

theorem cgrahl1
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
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  assume iscgra.p: |- P = ( Base ` G )
  assume iscgra.i: |- I = ( Itv ` G )
  assume iscgra.k: |- K = ( hlG ` G )
  assume iscgra.g: |- ( ph -> G e. TarskiG )
  assume iscgra.a: |- ( ph -> A e. P )
  assume iscgra.b: |- ( ph -> B e. P )
  assume iscgra.c: |- ( ph -> C e. P )
  assume iscgra.d: |- ( ph -> D e. P )
  assume iscgra.e: |- ( ph -> E e. P )
  assume iscgra.f: |- ( ph -> F e. P )
  assume cgrahl1.2: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
  assume cgrahl1.x: |- ( ph -> X e. P )
  assume cgrahl1.1: |- ( ph -> X ( K ` E ) D )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" X E F "> )

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
    wbr
    #
    @1
    cD
    cE
    cK
    cfv
    #
    wbr
    #
    @2
    cF
    @4
    wbr
    #
    w3a
    #
    @0
    cX
    cE
    cF
    cs3
    cG
    ccgra
    cfv
    #
    wbr
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
    @7
    wa
    #
    cA
    cB
    cC
    cX
    cP
    cE
    cF
    cG
    cI
    cK
    @1
    @2
    iscgra.p
    iscgra.i
    iscgra.k
    wph
    cG
    cstrkg
    wcel
    @9
    @11
    @7
    iscgra.g
    ad3antrrr
    #
    wph
    cA
    cP
    wcel
    @9
    @11
    @7
    iscgra.a
    ad3antrrr
    wph
    cB
    cP
    wcel
    @9
    @11
    @7
    iscgra.b
    ad3antrrr
    wph
    cC
    cP
    wcel
    @9
    @11
    @7
    iscgra.c
    ad3antrrr
    wph
    cX
    cP
    wcel
    @9
    @11
    @7
    cgrahl1.x
    ad3antrrr
    #
    wph
    cE
    cP
    wcel
    @9
    @11
    @7
    iscgra.e
    ad3antrrr
    #
    wph
    cF
    cP
    wcel
    @9
    @11
    @7
    iscgra.f
    ad3antrrr
    wph
    @9
    @11
    @7
    simpllr
    #
    @10
    @11
    @7
    simplr
    @12
    @3
    @5
    @6
    simpr1
    @13
    @1
    cD
    cX
    cE
    cP
    cG
    cI
    cK
    iscgra.p
    iscgra.i
    iscgra.k
    @17
    wph
    cD
    cP
    wcel
    @9
    @11
    @7
    iscgra.d
    ad3antrrr
    #
    @15
    @14
    @16
    @12
    @3
    @5
    @6
    simpr2
    @13
    cX
    cD
    cE
    cP
    cG
    cI
    cK
    cstrkg
    iscgra.p
    iscgra.i
    iscgra.k
    @15
    @18
    @16
    @14
    wph
    cX
    cD
    @4
    wbr
    @9
    @11
    @7
    cgrahl1.1
    ad3antrrr
    hlcomd
    hltr
    @12
    @3
    @5
    @6
    simpr3
    iscgrad
    wph
    @0
    cD
    cE
    cF
    cs3
    @8
    wbr
    @7
    vy
    cP
    wrex
    vx
    cP
    wrex
    cgrahl1.2
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
    cK
    iscgra.p
    iscgra.i
    iscgra.k
    iscgra.g
    iscgra.a
    iscgra.b
    iscgra.c
    iscgra.d
    iscgra.e
    iscgra.f
    iscgra
    mpbid
    r19.29vva
end
