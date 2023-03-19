include "cnrm.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "ccld.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "nrmtop.mm"
include "nrmsep.mm"
include "3exp2.mm"
include "impd.mm"
include "ralrimivv.mm"
include "jca.mm"
include "ccl.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "sslin.mm"
include "syl.mm"
include "cuni.mm"
include "cdif.mm"
include "simplll.mm"
include "simplr.mm"
include "eqid.mm"
include "opncld.mm"
include "syl2anc.mm"
include "simpr3.mm"
include "wb.mm"
include "simpllr.mm"
include "elssuni.mm"
include "reldisj.mm"
include "3syl.mm"
include "mpbid.mm"
include "clsss2.mm"
include "ssdifin0.mm"
include "sseq0.mm"
include "ex.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "imp.mm"
include "isnrm2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isnrm3
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
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
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint x y
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint J c
  disjoint d x
  disjoint d y
  disjoint J d
  disjoint J x
  disjoint J y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
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
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c z
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
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
  disjoint J o
  disjoint J u
  disjoint J v
  disjoint J w
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
  assert |- ( J e. Nrm <-> ( J e. Top /\ A. c e. ( Clsd ` J ) A. d e. ( Clsd ` J ) ( ( c i^i d ) = (/) -> E. x e. J E. y e. J ( c C_ x /\ d C_ y /\ ( x i^i y ) = (/) ) ) ) )

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
    c0
    wceq
    #
    @2
    vx
    cv
    #
    wss
    #
    @3
    vy
    cv
    #
    wss
    #
    @5
    @7
    cin
    c0
    wceq
    #
    w3a
    #
    vy
    cJ
    wrex
    #
    vx
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
    @4
    @12
    vx
    vy
    @2
    @3
    cJ
    nrmsep
    3exp2
    impd
    ralrimivv
    jca
    @17
    @1
    @4
    @6
    @5
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
    vx
    cJ
    wrex
    #
    wi
    #
    vd
    @14
    wral
    #
    vc
    @14
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
    @15
    @26
    vc
    @14
    @1
    @13
    @25
    vd
    @14
    @1
    @12
    @24
    @4
    @1
    @11
    @23
    vx
    cJ
    @1
    @5
    cJ
    wcel
    #
    wa
    #
    @10
    @23
    vy
    cJ
    @29
    @7
    cJ
    wcel
    #
    wa
    #
    @10
    @23
    @31
    @10
    wa
    #
    @6
    @22
    @31
    @6
    @8
    @9
    simpr1
    @32
    @21
    @20
    @7
    cin
    #
    wss
    #
    @33
    c0
    wceq
    #
    @22
    @32
    @8
    @34
    @31
    @6
    @8
    @9
    simpr2
    @3
    @7
    @20
    sslin
    syl
    @32
    cJ
    cuni
    #
    @7
    cdif
    #
    @14
    wcel
    #
    @5
    @37
    wss
    #
    @35
    @32
    @1
    @30
    @38
    @1
    @28
    @30
    @10
    simplll
    @29
    @30
    @10
    simplr
    @7
    cJ
    @36
    @36
    eqid
    #
    opncld
    syl2anc
    @32
    @9
    @39
    @31
    @6
    @8
    @9
    simpr3
    @32
    @28
    @5
    @36
    wss
    @9
    @39
    wb
    @1
    @28
    @30
    @10
    simpllr
    @5
    cJ
    elssuni
    @5
    @7
    @36
    reldisj
    3syl
    mpbid
    @38
    @39
    wa
    @20
    @37
    wss
    @35
    @37
    @5
    cJ
    @36
    @40
    clsss2
    @20
    @36
    @7
    ssdifin0
    syl
    syl2anc
    @21
    @33
    sseq0
    syl2anc
    jca
    ex
    rexlimdva
    reximdva
    imim2d
    ralimdv
    ralimdv
    imp
    vx
    cJ
    vc
    vd
    isnrm2
    sylanbrc
    impbii
end
