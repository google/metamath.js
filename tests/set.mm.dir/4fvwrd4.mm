include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "c1.mm"
include "c2.mm"
include "simpr.mm"
include "cn0.mm"
include "0nn0.mm"
include "elnn0uz.mm"
include "mpbi.mm"
include "wss.mm"
include "3nn0.mm"
include "uzss.mm"
include "ax-mp.mm"
include "sseli.mm"
include "eluzfz.mm"
include "sylancr.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "risset.mm"
include "eqcom.mm"
include "rexbii.mm"
include "bitri.mm"
include "sylib.mm"
include "1eluzge0.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "1z.mm"
include "3z.mm"
include "1le3.mm"
include "eluz2.mm"
include "mpbir3an.mm"
include "jca.mm"
include "2eluzge0.mm"
include "uzuzle23.mm"
include "mpan.mm"
include "jca32.mm"
include "r19.42v.mm"
include "anbi2i.mm"
include "2rexbii.mm"
include "r19.41v.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "sylibr.mm"

theorem 4fvwrd4
  let cP: class P
  let cL: class L
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V d
  assert |- ( ( L e. ( ZZ>= ` 3 ) /\ P : ( 0 ... L ) --> V ) -> E. a e. V E. b e. V E. c e. V E. d e. V ( ( ( P ` 0 ) = a /\ ( P ` 1 ) = b ) /\ ( ( P ` 2 ) = c /\ ( P ` 3 ) = d ) ) )

  proof
    cL
    c3
    cuz
    cfv
    #
    wcel
    #
    cc0
    cL
    cfz
    co
    #
    cV
    cP
    wf
    #
    wa
    #
    cc0
    cP
    cfv
    #
    va
    cv
    #
    wceq
    #
    va
    cV
    wrex
    #
    c1
    cP
    cfv
    #
    vb
    cv
    #
    wceq
    #
    vb
    cV
    wrex
    #
    wa
    #
    c2
    cP
    cfv
    #
    vc
    cv
    #
    wceq
    #
    vc
    cV
    wrex
    #
    c3
    cP
    cfv
    #
    vd
    cv
    #
    wceq
    #
    vd
    cV
    wrex
    #
    wa
    #
    wa
    #
    @7
    @11
    wa
    #
    @16
    @20
    wa
    #
    wa
    vd
    cV
    wrex
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    @4
    @13
    @17
    @21
    @4
    @8
    @12
    @4
    @5
    cV
    wcel
    #
    @8
    @4
    @2
    cV
    cc0
    cP
    @1
    @3
    simpr
    #
    @1
    cc0
    @2
    wcel
    #
    @3
    @1
    cc0
    cc0
    cuz
    cfv
    #
    wcel
    #
    cL
    @32
    wcel
    @31
    cc0
    cn0
    wcel
    @33
    0nn0
    cc0
    elnn0uz
    mpbi
    @0
    @32
    cL
    c3
    @32
    wcel
    #
    @0
    @32
    wss
    c3
    cn0
    wcel
    @34
    3nn0
    c3
    elnn0uz
    mpbi
    #
    cc0
    c3
    uzss
    ax-mp
    sseli
    cc0
    cc0
    cL
    eluzfz
    sylancr
    adantr
    ffvelrnd
    @29
    @6
    @5
    wceq
    #
    va
    cV
    wrex
    @8
    va
    @5
    cV
    risset
    @36
    @7
    va
    cV
    @6
    @5
    eqcom
    rexbii
    bitri
    sylib
    @4
    @9
    cV
    wcel
    #
    @12
    @4
    @2
    cV
    c1
    cP
    @30
    @1
    c1
    @2
    wcel
    #
    @3
    @1
    c1
    @32
    wcel
    cL
    c1
    cuz
    cfv
    #
    wcel
    @38
    1eluzge0
    @0
    @39
    cL
    c3
    @39
    wcel
    #
    @0
    @39
    wss
    @40
    c1
    cz
    wcel
    c3
    cz
    wcel
    c1
    c3
    cle
    wbr
    1z
    3z
    1le3
    c1
    c3
    eluz2
    mpbir3an
    c1
    c3
    uzss
    ax-mp
    sseli
    c1
    cc0
    cL
    eluzfz
    sylancr
    adantr
    ffvelrnd
    @37
    @10
    @9
    wceq
    #
    vb
    cV
    wrex
    @12
    vb
    @9
    cV
    risset
    @41
    @11
    vb
    cV
    @10
    @9
    eqcom
    rexbii
    bitri
    sylib
    jca
    @4
    @14
    cV
    wcel
    #
    @17
    @4
    @2
    cV
    c2
    cP
    @30
    @1
    c2
    @2
    wcel
    #
    @3
    @1
    c2
    @32
    wcel
    cL
    c2
    cuz
    cfv
    wcel
    @43
    2eluzge0
    cL
    uzuzle23
    c2
    cc0
    cL
    eluzfz
    sylancr
    adantr
    ffvelrnd
    @42
    @15
    @14
    wceq
    #
    vc
    cV
    wrex
    @17
    vc
    @14
    cV
    risset
    @44
    @16
    vc
    cV
    @15
    @14
    eqcom
    rexbii
    bitri
    sylib
    @4
    @18
    cV
    wcel
    #
    @21
    @4
    @2
    cV
    c3
    cP
    @30
    @1
    c3
    @2
    wcel
    #
    @3
    @34
    @1
    @46
    @35
    c3
    cc0
    cL
    eluzfz
    mpan
    adantr
    ffvelrnd
    @45
    @19
    @18
    wceq
    #
    vd
    cV
    wrex
    @21
    vd
    @18
    cV
    risset
    @47
    @20
    vd
    cV
    @19
    @18
    eqcom
    rexbii
    bitri
    sylib
    jca32
    @28
    @24
    @16
    @21
    wa
    #
    wa
    #
    vc
    cV
    wrex
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    @24
    @22
    wa
    #
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    #
    @23
    @27
    @50
    va
    vb
    cV
    cV
    @26
    @49
    vc
    cV
    @26
    @24
    @25
    vd
    cV
    wrex
    #
    wa
    @49
    @24
    @25
    vd
    cV
    r19.42v
    @54
    @48
    @24
    @16
    @20
    vd
    cV
    r19.42v
    anbi2i
    bitri
    rexbii
    2rexbii
    @50
    @51
    va
    vb
    cV
    cV
    @50
    @24
    @48
    vc
    cV
    wrex
    #
    wa
    @51
    @24
    @48
    vc
    cV
    r19.42v
    @55
    @22
    @24
    @16
    @21
    vc
    cV
    r19.41v
    anbi2i
    bitri
    2rexbii
    @53
    @7
    @12
    wa
    #
    @22
    wa
    #
    va
    cV
    wrex
    @56
    va
    cV
    wrex
    #
    @22
    wa
    @23
    @52
    @57
    va
    cV
    @52
    @24
    vb
    cV
    wrex
    #
    @22
    wa
    @57
    @24
    @22
    vb
    cV
    r19.41v
    @59
    @56
    @22
    @7
    @11
    vb
    cV
    r19.42v
    anbi1i
    bitri
    rexbii
    @56
    @22
    va
    cV
    r19.41v
    @58
    @13
    @22
    @7
    @12
    va
    cV
    r19.41v
    anbi1i
    3bitri
    3bitri
    sylibr
end
