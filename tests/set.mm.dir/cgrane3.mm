include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "simpllr.mm"
include "ad3antrrr.mm"
include "simpr2.mm"
include "hlne2.mm"
include "necomd.mm"
include "ccgra.mm"
include "wrex.mm"
include "iscgra.mm"
include "mpbid.mm"
include "r19.29vva.mm"

theorem cgrane3
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


  assert |- ( ph -> E =/= D )

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
    cE
    cD
    wne
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
    @2
    cP
    wcel
    #
    wa
    #
    @7
    wa
    #
    cD
    cE
    @11
    @1
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
    wph
    @8
    @9
    @7
    simpllr
    wph
    cD
    cP
    wcel
    @8
    @9
    @7
    iscgra.d
    ad3antrrr
    wph
    cE
    cP
    wcel
    @8
    @9
    @7
    iscgra.e
    ad3antrrr
    wph
    cG
    cstrkg
    wcel
    @8
    @9
    @7
    iscgra.g
    ad3antrrr
    @10
    @3
    @5
    @6
    simpr2
    hlne2
    necomd
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
