include "cs3.mm"
include "ccgra.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ccgrg.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "3jca.mm"
include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "s3eqd.mm"
include "breq2d.mm"
include "breq1.mm"
include "3anbi12d.mm"
include "3anbi13d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "iscgra.mm"
include "mpbird.mm"

theorem iscgrad
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
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
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
  assume iscgrad.x: |- ( ph -> X e. P )
  assume iscgrad.y: |- ( ph -> Y e. P )
  assume iscgrad.1: |- ( ph -> <" A B C "> ( cgrG ` G ) <" X E Y "> )
  assume iscgrad.2: |- ( ph -> X ( K ` E ) D )
  assume iscgrad.3: |- ( ph -> Y ( K ` E ) F )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    cF
    cs3
    cG
    ccgra
    cfv
    wbr
    @0
    vx
    cv
    #
    cE
    vy
    cv
    #
    cs3
    #
    cG
    ccgrg
    cfv
    #
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
    @6
    wbr
    #
    w3a
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    @0
    cX
    cE
    cY
    cs3
    #
    @4
    wbr
    #
    cX
    cD
    @6
    wbr
    #
    cY
    cF
    @6
    wbr
    #
    w3a
    #
    @10
    iscgrad.x
    iscgrad.y
    wph
    @12
    @13
    @14
    iscgrad.1
    iscgrad.2
    iscgrad.3
    3jca
    @9
    @15
    @0
    cX
    cE
    @2
    cs3
    #
    @4
    wbr
    #
    @13
    @8
    w3a
    vx
    vy
    cX
    cY
    cP
    cP
    @1
    cX
    wceq
    #
    @5
    @17
    @7
    @13
    @8
    @18
    @3
    @16
    @0
    @4
    @18
    @1
    cE
    @2
    @2
    cX
    cE
    @18
    id
    @18
    cE
    eqidd
    @18
    @2
    eqidd
    s3eqd
    breq2d
    @1
    cX
    cD
    @6
    breq1
    3anbi12d
    @2
    cY
    wceq
    #
    @17
    @12
    @8
    @14
    @13
    @19
    @16
    @11
    @0
    @4
    @19
    cX
    cE
    @2
    cY
    cX
    cE
    @19
    cX
    eqidd
    @19
    cE
    eqidd
    @19
    id
    s3eqd
    breq2d
    @2
    cY
    cF
    @6
    breq1
    3anbi13d
    rspc2ev
    syl3anc
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
    mpbird
end
