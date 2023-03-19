include "chil.mm"
include "wcel.mm"
include "cfv.mm"
include "cno.mm"
include "cnop.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "breq1.mm"
include "wne.mm"
include "wa.mm"
include "csp.mm"
include "cabs.mm"
include "cc.mm"
include "cnlnadjlem4.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "syl.mm"
include "hicl.mm"
include "mpancom.mm"
include "abscld.mm"
include "cr.mm"
include "normcl.mm"
include "remulcld.mm"
include "nmcopexi.mm"
include "remulcl.mm"
include "sylancr.mm"
include "bcs.mm"
include "normge0.mm"
include "nmcoplbi.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "wceq.mm"
include "cnlnadjlem5.mm"
include "mpdan.mm"
include "fveq2d.mm"
include "hiidrcl.mm"
include "hiidge0.mm"
include "absidd.mm"
include "c2.mm"
include "cexp.mm"
include "normsq.mm"
include "recnd.mm"
include "sqvald.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"
include "recni.mm"
include "mul32.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "3brtr3d.mm"
include "adantr.mm"
include "clt.mm"
include "wb.mm"
include "0re.mm"
include "leltne.mm"
include "biimpar.mm"
include "sylan.mm"
include "lemul1.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "wf.mm"
include "nmopge0.mm"
include "ax-mp.mm"
include "mulge0.mm"
include "mpanl12.mm"
include "pm2.61ne.mm"

theorem cnlnadjlem7
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let vt: setvar t
  let vx: setvar x
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )
  assume cnlnadjlem.5: |- F = ( y e. ~H |-> B )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint A g
  disjoint v w
  disjoint v y
  disjoint A v
  disjoint w y
  disjoint A w
  disjoint A y
  disjoint F w
  disjoint T g
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint G v
  disjoint G w
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g z
  disjoint v z
  disjoint w z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint T f
  disjoint g t
  disjoint g x
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G x
  disjoint G z
  assert |- ( A e. ~H -> ( normh ` ( F ` A ) ) <_ ( ( normop ` T ) x. ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cF
    cfv
    #
    cno
    cfv
    #
    cT
    cnop
    cfv
    #
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cc0
    @5
    cle
    wbr
    #
    @2
    cc0
    @2
    cc0
    @5
    cle
    breq1
    @0
    @2
    cc0
    wne
    #
    wa
    #
    @6
    @2
    @2
    cmul
    co
    #
    @5
    @2
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @12
    @8
    @0
    @1
    cT
    cfv
    #
    cA
    csp
    co
    #
    cabs
    cfv
    #
    @3
    @2
    cmul
    co
    #
    @4
    cmul
    co
    #
    @10
    @11
    cle
    @0
    @15
    @13
    cno
    cfv
    #
    @4
    cmul
    co
    #
    @17
    @0
    @14
    @13
    chil
    wcel
    #
    @0
    @14
    cc
    wcel
    @0
    @1
    chil
    wcel
    #
    @20
    vy
    vw
    vv
    cA
    cB
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem4
    #
    chil
    chil
    @1
    cT
    cT
    cnlnadjlem.1
    lnopfi
    #
    ffvelrni
    syl
    #
    @13
    cA
    hicl
    mpancom
    abscld
    @0
    @18
    @4
    @0
    @20
    @18
    cr
    wcel
    @24
    @13
    normcl
    syl
    #
    cA
    normcl
    #
    remulcld
    @0
    @16
    @4
    @0
    @3
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @16
    cr
    wcel
    cT
    cnlnadjlem.1
    cnlnadjlem.2
    nmcopexi
    #
    @0
    @21
    @28
    @22
    @1
    normcl
    #
    syl
    #
    @3
    @2
    remulcl
    sylancr
    #
    @26
    remulcld
    @20
    @0
    @15
    @19
    cle
    wbr
    @24
    @13
    cA
    bcs
    mpancom
    @0
    @18
    @16
    @4
    @25
    @32
    @26
    cA
    normge0
    #
    @0
    @21
    @18
    @16
    cle
    wbr
    @22
    @1
    cT
    cnlnadjlem.1
    cnlnadjlem.2
    nmcoplbi
    syl
    lemul1ad
    letrd
    @0
    @15
    @1
    @1
    csp
    co
    #
    cabs
    cfv
    @34
    @10
    @0
    @14
    @34
    cabs
    @0
    @21
    @14
    @34
    wceq
    @22
    vy
    vw
    vv
    cA
    cB
    @1
    cT
    vg
    cF
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem.4
    cnlnadjlem.5
    cnlnadjlem5
    mpdan
    fveq2d
    @0
    @34
    @0
    @21
    @34
    cr
    wcel
    @22
    @1
    hiidrcl
    syl
    @0
    @21
    cc0
    @34
    cle
    wbr
    @22
    @1
    hiidge0
    syl
    absidd
    @0
    @2
    c2
    cexp
    co
    #
    @34
    @10
    @0
    @21
    @35
    @34
    wceq
    @22
    @1
    normsq
    syl
    @0
    @2
    @0
    @2
    @31
    recnd
    #
    sqvald
    eqtr3d
    3eqtrd
    @0
    @2
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @17
    @11
    wceq
    #
    @36
    @0
    @4
    @26
    recnd
    @3
    cc
    wcel
    @37
    @38
    @39
    @3
    @29
    recni
    @3
    @2
    @4
    mul32
    mp3an1
    syl2anc
    3brtr3d
    adantr
    @9
    @28
    @5
    cr
    wcel
    #
    @28
    cc0
    @2
    clt
    wbr
    #
    @6
    @12
    wb
    @0
    @28
    @8
    @31
    adantr
    #
    @0
    @40
    @8
    @0
    @27
    @4
    cr
    wcel
    #
    @40
    @29
    @26
    @3
    @4
    remulcl
    sylancr
    adantr
    @42
    @0
    @21
    @8
    @41
    @22
    @21
    @41
    @8
    @21
    @28
    cc0
    @2
    cle
    wbr
    #
    @41
    @8
    wb
    #
    @30
    @1
    normge0
    cc0
    cr
    wcel
    @28
    @44
    @45
    0re
    cc0
    @2
    leltne
    mp3an1
    syl2anc
    biimpar
    sylan
    @2
    @5
    @2
    lemul1
    syl112anc
    mpbird
    @0
    @43
    cc0
    @4
    cle
    wbr
    #
    @7
    @26
    @33
    @27
    cc0
    @3
    cle
    wbr
    #
    @43
    @46
    wa
    @7
    @29
    chil
    chil
    cT
    wf
    @47
    @23
    cT
    nmopge0
    ax-mp
    @3
    @4
    mulge0
    mpanl12
    syl2anc
    pm2.61ne
end
