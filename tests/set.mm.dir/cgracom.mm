include "cs3.mm"
include "ccgra.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ccgrg.mm"
include "w3a.mm"
include "wrex.mm"
include "cds.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprlr.mm"
include "eqcomd.mm"
include "tgcgrcomlr.mm"
include "simprrr.mm"
include "simprll.mm"
include "simprrl.mm"
include "cgracgr.mm"
include "trgcgr.mm"
include "3jca.mm"
include "cgrane1.mm"
include "cgrane3.mm"
include "hlcgrex.mm"
include "cgrane2.mm"
include "necomd.mm"
include "cgrane4.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "reximddv2.mm"
include "iscgra.mm"
include "mpbird.mm"

theorem cgracom
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
  let vx: setvar x
  let vy: setvar y
  assume cgraid.p: |- P = ( Base ` G )
  assume cgraid.i: |- I = ( Itv ` G )
  assume cgraid.g: |- ( ph -> G e. TarskiG )
  assume cgraid.k: |- K = ( hlG ` G )
  assume cgraid.a: |- ( ph -> A e. P )
  assume cgraid.b: |- ( ph -> B e. P )
  assume cgraid.c: |- ( ph -> C e. P )
  assume cgracom.d: |- ( ph -> D e. P )
  assume cgracom.e: |- ( ph -> E e. P )
  assume cgracom.f: |- ( ph -> F e. P )
  assume cgracom.1: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )


  assert |- ( ph -> <" D E F "> ( cgrA ` G ) <" A B C "> )

  proof
    wph
    cD
    cE
    cF
    cs3
    #
    cA
    cB
    cC
    cs3
    #
    cG
    ccgra
    cfv
    #
    wbr
    @0
    vx
    cv
    #
    cB
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
    @3
    cA
    cB
    cK
    cfv
    #
    wbr
    #
    @4
    cC
    @7
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
    wph
    @8
    cB
    @3
    cG
    cds
    cfv
    #
    co
    #
    cE
    cD
    @11
    co
    #
    wceq
    #
    wa
    #
    @9
    cB
    @4
    @11
    co
    #
    cE
    cF
    @11
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @10
    vx
    vy
    cP
    cP
    wph
    @3
    cP
    wcel
    #
    wa
    #
    @4
    cP
    wcel
    #
    wa
    #
    @20
    wa
    #
    @6
    @8
    @9
    @25
    cD
    cE
    cF
    @3
    cP
    @5
    cB
    @4
    cG
    @11
    cgraid.p
    @11
    eqid
    #
    @5
    eqid
    wph
    cG
    cstrkg
    wcel
    @21
    @23
    @20
    cgraid.g
    ad3antrrr
    #
    wph
    cD
    cP
    wcel
    @21
    @23
    @20
    cgracom.d
    ad3antrrr
    #
    wph
    cE
    cP
    wcel
    @21
    @23
    @20
    cgracom.e
    ad3antrrr
    #
    wph
    cF
    cP
    wcel
    @21
    @23
    @20
    cgracom.f
    ad3antrrr
    #
    wph
    @21
    @23
    @20
    simpllr
    #
    wph
    cB
    cP
    wcel
    @21
    @23
    @20
    cgraid.b
    ad3antrrr
    #
    @22
    @23
    @20
    simplr
    #
    @25
    cE
    cD
    cB
    @3
    cP
    cG
    cI
    @11
    cgraid.p
    @26
    cgraid.i
    @27
    @29
    @28
    @32
    @31
    @25
    @12
    @13
    @24
    @8
    @14
    @19
    simprlr
    #
    eqcomd
    tgcgrcomlr
    @25
    @16
    @17
    @24
    @15
    @9
    @18
    simprrr
    #
    eqcomd
    @25
    cD
    cF
    @3
    @4
    cP
    cG
    cI
    @11
    cgraid.p
    @26
    cgraid.i
    @27
    @28
    @30
    @31
    @33
    @25
    @3
    @4
    @11
    co
    cD
    cF
    @11
    co
    @25
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
    @11
    @3
    @4
    cgraid.p
    cgraid.i
    cgraid.k
    @27
    wph
    cA
    cP
    wcel
    @21
    @23
    @20
    cgraid.a
    ad3antrrr
    @32
    wph
    cC
    cP
    wcel
    @21
    @23
    @20
    cgraid.c
    ad3antrrr
    @28
    @29
    @30
    wph
    @1
    @0
    @2
    wbr
    @21
    @23
    @20
    cgracom.1
    ad3antrrr
    @31
    @26
    @33
    @24
    @8
    @14
    @19
    simprll
    #
    @24
    @15
    @9
    @18
    simprrl
    #
    @34
    @35
    cgracgr
    eqcomd
    tgcgrcomlr
    trgcgr
    @36
    @37
    3jca
    wph
    @15
    vx
    cP
    wrex
    @19
    vy
    cP
    wrex
    @20
    vy
    cP
    wrex
    vx
    cP
    wrex
    wph
    vx
    cB
    cE
    cD
    cA
    cP
    cG
    cI
    cK
    @11
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.b
    cgracom.e
    cgracom.d
    cgraid.g
    cgraid.a
    @26
    wph
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
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgracom.1
    cgrane1
    wph
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
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgracom.1
    cgrane3
    hlcgrex
    wph
    vy
    cB
    cE
    cF
    cC
    cP
    cG
    cI
    cK
    @11
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.b
    cgracom.e
    cgracom.f
    cgraid.g
    cgraid.c
    @26
    wph
    cB
    cC
    wph
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
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgracom.1
    cgrane2
    necomd
    wph
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
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgracom.d
    cgracom.e
    cgracom.f
    cgracom.1
    cgrane4
    hlcgrex
    @15
    @19
    vx
    vy
    cP
    cP
    reeanv
    sylanbrc
    reximddv2
    wph
    vx
    vy
    cD
    cE
    cF
    cA
    cP
    cB
    cC
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgracom.d
    cgracom.e
    cgracom.f
    cgraid.a
    cgraid.b
    cgraid.c
    iscgra
    mpbird
end
