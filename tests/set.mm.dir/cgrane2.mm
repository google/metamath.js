include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wne.mm"
include "wcel.mm"
include "wa.mm"
include "cds.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "co.mm"
include "simpllr.mm"
include "simpr1.mm"
include "cgr3simp2.mm"
include "eqcomd.mm"
include "simpr3.mm"
include "hlne1.mm"
include "necomd.mm"
include "tgcgrneq.mm"
include "ccgra.mm"
include "wrex.mm"
include "iscgra.mm"
include "mpbid.mm"
include "r19.29vva.mm"

theorem cgrane2
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


  assert |- ( ph -> B =/= C )

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
    cK
    cfv
    #
    wbr
    #
    @2
    cF
    @5
    wbr
    #
    w3a
    #
    cB
    cC
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
    #
    @2
    cP
    wcel
    #
    wa
    #
    @8
    wa
    #
    cE
    @2
    cB
    cC
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    iscgra.p
    @14
    eqid
    #
    iscgra.i
    wph
    cG
    cstrkg
    wcel
    @9
    @11
    @8
    iscgra.g
    ad3antrrr
    #
    wph
    cE
    cP
    wcel
    @9
    @11
    @8
    iscgra.e
    ad3antrrr
    #
    @10
    @11
    @8
    simplr
    #
    wph
    cB
    cP
    wcel
    @9
    @11
    @8
    iscgra.b
    ad3antrrr
    #
    wph
    cC
    cP
    wcel
    @9
    @11
    @8
    iscgra.c
    ad3antrrr
    #
    @13
    cB
    cC
    @14
    co
    cE
    @2
    @14
    co
    @13
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
    @14
    iscgra.p
    @15
    iscgra.i
    @3
    eqid
    @16
    wph
    cA
    cP
    wcel
    @9
    @11
    @8
    iscgra.a
    ad3antrrr
    @19
    @20
    wph
    @9
    @11
    @8
    simpllr
    @17
    @18
    @12
    @4
    @6
    @7
    simpr1
    cgr3simp2
    eqcomd
    @13
    @2
    cE
    @13
    @2
    cF
    cE
    cP
    cG
    cI
    cK
    cstrkg
    iscgra.p
    iscgra.i
    iscgra.k
    @18
    wph
    cF
    cP
    wcel
    @9
    @11
    @8
    iscgra.f
    ad3antrrr
    @17
    @16
    @12
    @4
    @6
    @7
    simpr3
    hlne1
    necomd
    tgcgrneq
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
    @8
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
