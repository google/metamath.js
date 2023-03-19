include "cs3.mm"
include "cv.mm"
include "ccgrg.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wcel.mm"
include "wa.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "cstrkg.mm"
include "simpllr.mm"
include "simpr2.mm"
include "hlcomd.mm"
include "wne.mm"
include "co.mm"
include "wo.mm"
include "hlne1.mm"
include "simpr3.mm"
include "eqid.mm"
include "adantr.mm"
include "ad4antr.mm"
include "simplr1.mm"
include "cgr3swap23.mm"
include "cgr3rotr.mm"
include "simpr.mm"
include "tgbtwnxfr.mm"
include "orcd.mm"
include "cgr3rotl.mm"
include "olcd.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp3d.mm"
include "mpjaodan.mm"
include "3jca.mm"
include "mpbird.mm"
include "hltr.mm"
include "ccgra.mm"
include "wrex.mm"
include "iscgra.mm"
include "r19.29vva.mm"

theorem cgrahl
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
  assume cgrahl.k: |- K = ( hlG ` G )
  assume cgrahl.2: |- ( ph -> A ( K ` B ) C )


  assert |- ( ph -> D ( K ` E ) F )

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
    cD
    cF
    @5
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
    @8
    wa
    #
    cD
    @2
    cF
    cE
    cP
    cG
    cI
    cK
    cgracol.p
    cgracol.i
    cgrahl.k
    wph
    cD
    cP
    wcel
    @9
    @11
    @8
    cgracol.d
    ad3antrrr
    #
    @10
    @11
    @8
    simplr
    #
    wph
    cF
    cP
    wcel
    @9
    @11
    @8
    cgracol.f
    ad3antrrr
    #
    wph
    cG
    cstrkg
    wcel
    #
    @9
    @11
    @8
    cgracol.g
    ad3antrrr
    #
    wph
    cE
    cP
    wcel
    #
    @9
    @11
    @8
    cgracol.e
    ad3antrrr
    #
    @13
    cD
    @1
    @2
    cE
    cP
    cG
    cI
    cK
    cgracol.p
    cgracol.i
    cgrahl.k
    @14
    wph
    @9
    @11
    @8
    simpllr
    #
    @15
    @18
    @20
    @13
    @1
    cD
    cE
    cP
    cG
    cI
    cK
    cstrkg
    cgracol.p
    cgracol.i
    cgrahl.k
    @21
    @14
    @20
    @18
    @12
    @4
    @6
    @7
    simpr2
    #
    hlcomd
    @13
    @1
    @2
    @5
    wbr
    @1
    cE
    wne
    #
    @2
    cE
    wne
    #
    @1
    cE
    @2
    cI
    co
    wcel
    #
    @2
    cE
    @1
    cI
    co
    wcel
    #
    wo
    #
    w3a
    @13
    @23
    @24
    @27
    @13
    @1
    cD
    cE
    cP
    cG
    cI
    cK
    cstrkg
    cgracol.p
    cgracol.i
    cgrahl.k
    @21
    @14
    @20
    @18
    @22
    hlne1
    @13
    @2
    cF
    cE
    cP
    cG
    cI
    cK
    cstrkg
    cgracol.p
    cgracol.i
    cgrahl.k
    @15
    @16
    @20
    @18
    @12
    @4
    @6
    @7
    simpr3
    #
    hlne1
    @13
    cA
    cB
    cC
    cI
    co
    wcel
    #
    @27
    cC
    cB
    cA
    cI
    co
    wcel
    #
    @13
    @29
    wa
    #
    @25
    @26
    @31
    cB
    cA
    cC
    cE
    cP
    @3
    @1
    @2
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @3
    eqid
    #
    @13
    @17
    @29
    @18
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @9
    @11
    @8
    @29
    cgracol.b
    ad4antr
    #
    wph
    cA
    cP
    wcel
    #
    @9
    @11
    @8
    @29
    cgracol.a
    ad4antr
    #
    wph
    cC
    cP
    wcel
    #
    @9
    @11
    @8
    @29
    cgracol.c
    ad4antr
    #
    @13
    @19
    @29
    @20
    adantr
    #
    @13
    @9
    @29
    @21
    adantr
    #
    @13
    @11
    @29
    @15
    adantr
    #
    @31
    cA
    cC
    cB
    @1
    cP
    @3
    @2
    cE
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @32
    @33
    @37
    @39
    @35
    @41
    @42
    @40
    @31
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
    @32
    @33
    @37
    @35
    @39
    @41
    @40
    @42
    @4
    @6
    @7
    @12
    @29
    simplr1
    cgr3swap23
    cgr3rotr
    @13
    @29
    simpr
    tgbtwnxfr
    orcd
    @13
    @30
    wa
    #
    @26
    @25
    @43
    cB
    cC
    cA
    cE
    cP
    @3
    @2
    @1
    cG
    cI
    c.mi
    cgracol.p
    cgracol.m
    cgracol.i
    @32
    wph
    @17
    @9
    @11
    @8
    @30
    cgracol.g
    ad4antr
    #
    wph
    @34
    @9
    @11
    @8
    @30
    cgracol.b
    ad4antr
    #
    wph
    @38
    @9
    @11
    @8
    @30
    cgracol.c
    ad4antr
    #
    wph
    @36
    @9
    @11
    @8
    @30
    cgracol.a
    ad4antr
    #
    wph
    @19
    @9
    @11
    @8
    @30
    cgracol.e
    ad4antr
    #
    @13
    @11
    @30
    @15
    adantr
    #
    @13
    @9
    @30
    @21
    adantr
    #
    @43
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
    @32
    @44
    @47
    @45
    @46
    @50
    @48
    @49
    @4
    @6
    @7
    @12
    @30
    simplr1
    cgr3rotl
    @13
    @30
    simpr
    tgbtwnxfr
    olcd
    wph
    @29
    @30
    wo
    #
    @9
    @11
    @8
    wph
    cA
    cB
    wne
    #
    cC
    cB
    wne
    #
    @51
    wph
    cA
    cC
    cB
    cK
    cfv
    wbr
    @52
    @53
    @51
    w3a
    cgrahl.2
    wph
    cA
    cC
    cB
    cP
    cG
    cI
    cK
    cstrkg
    cgracol.p
    cgracol.i
    cgrahl.k
    cgracol.a
    cgracol.c
    cgracol.b
    cgracol.g
    ishlg
    mpbid
    simp3d
    ad3antrrr
    mpjaodan
    3jca
    @13
    @1
    @2
    cE
    cP
    cG
    cI
    cK
    cstrkg
    cgracol.p
    cgracol.i
    cgrahl.k
    @21
    @15
    @20
    @18
    ishlg
    mpbird
    hltr
    @28
    hltr
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
    cK
    cgracol.p
    cgracol.i
    cgrahl.k
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
