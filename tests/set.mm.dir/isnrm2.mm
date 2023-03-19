include "cnrm.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "ccld.mm"
include "wral.mm"
include "nrmtop.mm"
include "nrmsep2.mm"
include "3exp2.mm"
include "impd.mm"
include "ralrimivv.mm"
include "jca.mm"
include "cpw.mm"
include "simpl.mm"
include "cuni.mm"
include "cdif.mm"
include "eqid.mm"
include "opncld.mm"
include "adantr.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "inssdif0.mm"
include "cldss.mm"
include "adantl.mm"
include "df-ss.mm"
include "sylib.mm"
include "sseq1d.mm"
include "syl5bbr.mm"
include "simpll.mm"
include "elssuni.mm"
include "clsss3.mm"
include "syl2an.mm"
include "rexbidva.mm"
include "sylibd.mm"
include "ralimdva.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "impexp.mm"
include "ralbii2.mm"
include "syl6ibr.mm"
include "ralrimdva.mm"
include "imp.mm"
include "isnrm.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isnrm2
  let vo: setvar o
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vj: setvar j
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint c d
  disjoint c o
  disjoint J c
  disjoint d o
  disjoint J d
  disjoint J o
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint K u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint J f
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g o
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint J g
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint J m
  disjoint n o
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X o
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( J e. Nrm <-> ( J e. Top /\ A. c e. ( Clsd ` J ) A. d e. ( Clsd ` J ) ( ( c i^i d ) = (/) -> E. o e. J ( c C_ o /\ ( ( ( cls ` J ) ` o ) i^i d ) = (/) ) ) ) )

  proof
    cJ
    cnrm
    wcel
    #
    cJ
    ctop
    wcel
    #
    vc
    cv
    #
    vd
    cv
    #
    cin
    #
    c0
    wceq
    #
    @2
    vo
    cv
    #
    wss
    #
    @6
    cJ
    ccl
    cfv
    cfv
    #
    @3
    cin
    #
    c0
    wceq
    #
    wa
    #
    vo
    cJ
    wrex
    #
    wi
    #
    vd
    cJ
    ccld
    cfv
    #
    wral
    #
    vc
    @14
    wral
    #
    wa
    #
    @0
    @1
    @16
    cJ
    nrmtop
    @0
    @13
    vc
    vd
    @14
    @14
    @0
    @2
    @14
    wcel
    #
    @3
    @14
    wcel
    #
    @13
    @0
    @18
    @19
    @5
    @12
    vo
    @2
    @3
    cJ
    nrmsep2
    3exp2
    impd
    ralrimivv
    jca
    @17
    @1
    @7
    @8
    vx
    cv
    #
    wss
    #
    wa
    #
    vo
    cJ
    wrex
    #
    vc
    @14
    @20
    cpw
    #
    cin
    #
    wral
    #
    vx
    cJ
    wral
    #
    @0
    @1
    @16
    simpl
    @1
    @16
    @27
    @1
    @16
    @26
    vx
    cJ
    @1
    @20
    cJ
    wcel
    #
    wa
    #
    @16
    @2
    @20
    wss
    #
    @23
    wi
    #
    vc
    @14
    wral
    @26
    @29
    @15
    @31
    vc
    @14
    @29
    @18
    wa
    #
    @15
    @2
    cJ
    cuni
    #
    @20
    cdif
    #
    cin
    #
    c0
    wceq
    #
    @7
    @8
    @34
    cin
    #
    c0
    wceq
    #
    wa
    #
    vo
    cJ
    wrex
    #
    wi
    #
    @31
    @32
    @34
    @14
    wcel
    #
    @15
    @41
    wi
    @29
    @42
    @18
    @20
    cJ
    @33
    @33
    eqid
    #
    opncld
    adantr
    @13
    @41
    vd
    @34
    @14
    @3
    @34
    wceq
    #
    @5
    @36
    @12
    @40
    @44
    @4
    @35
    c0
    @3
    @34
    @2
    ineq2
    eqeq1d
    @44
    @11
    @39
    vo
    cJ
    @44
    @10
    @38
    @7
    @44
    @9
    @37
    c0
    @3
    @34
    @8
    ineq2
    eqeq1d
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl
    @32
    @36
    @30
    @40
    @23
    @36
    @2
    @33
    cin
    #
    @20
    wss
    @32
    @30
    @2
    @33
    @20
    inssdif0
    @32
    @45
    @2
    @20
    @32
    @2
    @33
    wss
    #
    @45
    @2
    wceq
    @18
    @46
    @29
    @2
    cJ
    @33
    @43
    cldss
    adantl
    @2
    @33
    df-ss
    sylib
    sseq1d
    syl5bbr
    @32
    @39
    @22
    vo
    cJ
    @32
    @6
    cJ
    wcel
    #
    wa
    #
    @38
    @21
    @7
    @38
    @8
    @33
    cin
    #
    @20
    wss
    @48
    @21
    @8
    @33
    @20
    inssdif0
    @48
    @49
    @8
    @20
    @48
    @8
    @33
    wss
    #
    @49
    @8
    wceq
    @32
    @1
    @6
    @33
    wss
    @50
    @47
    @1
    @28
    @18
    simpll
    @6
    cJ
    elssuni
    @6
    cJ
    @33
    @43
    clsss3
    syl2an
    @8
    @33
    df-ss
    sylib
    sseq1d
    syl5bbr
    anbi2d
    rexbidva
    imbi12d
    sylibd
    ralimdva
    @23
    @31
    vc
    @25
    @14
    @2
    @25
    wcel
    #
    @23
    wi
    @18
    @30
    wa
    #
    @23
    wi
    @18
    @31
    wi
    @51
    @52
    @23
    @51
    @18
    @2
    @24
    wcel
    #
    wa
    @52
    @2
    @14
    @24
    elin
    @53
    @30
    @18
    vc
    @20
    selpw
    anbi2i
    bitri
    imbi1i
    @18
    @30
    @23
    impexp
    bitri
    ralbii2
    syl6ibr
    ralrimdva
    imp
    vx
    vc
    vo
    cJ
    isnrm
    sylanbrc
    impbii
end
