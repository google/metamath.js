include "cnrm.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "ccl.mm"
include "wrex.mm"
include "cuni.mm"
include "cdif.mm"
include "ctop.mm"
include "nrmtop.mm"
include "ad2antrr.mm"
include "elssuni.mm"
include "ad2antrl.mm"
include "eqid.mm"
include "clscld.mm"
include "syl2anc.mm"
include "cldopn.mm"
include "syl.mm"
include "simprrl.mm"
include "incom.mm"
include "simprrr.mm"
include "syl5eq.mm"
include "wb.mm"
include "simplr2.mm"
include "cldss.mm"
include "reldisj.mm"
include "3syl.mm"
include "mpbid.mm"
include "sscls.mm"
include "ssrin.mm"
include "disjdif.mm"
include "sseq0.mm"
include "sylancl.mm"
include "sseq2.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "3anbi23d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "nrmsep2.mm"
include "reximddv.mm"

theorem nrmsep
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
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
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
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
  assert |- ( ( J e. Nrm /\ ( C e. ( Clsd ` J ) /\ D e. ( Clsd ` J ) /\ ( C i^i D ) = (/) ) ) -> E. x e. J E. y e. J ( C C_ x /\ D C_ y /\ ( x i^i y ) = (/) ) )

  proof
    cJ
    cnrm
    wcel
    #
    cC
    cJ
    ccld
    cfv
    #
    wcel
    #
    cD
    @1
    wcel
    #
    cC
    cD
    cin
    c0
    wceq
    #
    w3a
    #
    wa
    #
    cC
    vx
    cv
    #
    wss
    #
    @7
    cJ
    ccl
    cfv
    cfv
    #
    cD
    cin
    #
    c0
    wceq
    #
    wa
    #
    @8
    cD
    vy
    cv
    #
    wss
    #
    @7
    @13
    cin
    #
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
    @6
    @7
    cJ
    wcel
    #
    @12
    wa
    #
    wa
    #
    cJ
    cuni
    #
    @9
    cdif
    #
    cJ
    wcel
    #
    @8
    cD
    @23
    wss
    #
    @7
    @23
    cin
    #
    c0
    wceq
    #
    @18
    @21
    @9
    @1
    wcel
    #
    @24
    @21
    cJ
    ctop
    wcel
    #
    @7
    @22
    wss
    #
    @28
    @0
    @29
    @5
    @20
    cJ
    nrmtop
    ad2antrr
    #
    @19
    @30
    @6
    @12
    @7
    cJ
    elssuni
    ad2antrl
    #
    @7
    cJ
    @22
    @22
    eqid
    #
    clscld
    syl2anc
    @9
    cJ
    @22
    @33
    cldopn
    syl
    @6
    @19
    @8
    @11
    simprrl
    @21
    cD
    @9
    cin
    #
    c0
    wceq
    #
    @25
    @21
    @34
    @10
    c0
    cD
    @9
    incom
    @6
    @19
    @8
    @11
    simprrr
    syl5eq
    @21
    @3
    cD
    @22
    wss
    @35
    @25
    wb
    @2
    @3
    @4
    @0
    @20
    simplr2
    cD
    cJ
    @22
    @33
    cldss
    cD
    @9
    @22
    reldisj
    3syl
    mpbid
    @21
    @26
    @9
    @23
    cin
    #
    wss
    #
    @36
    c0
    wceq
    @27
    @21
    @7
    @9
    wss
    #
    @37
    @21
    @29
    @30
    @38
    @31
    @32
    @7
    cJ
    @22
    @33
    sscls
    syl2anc
    @7
    @9
    @23
    ssrin
    syl
    @9
    @22
    disjdif
    @26
    @36
    sseq0
    sylancl
    @17
    @8
    @25
    @27
    w3a
    vy
    @23
    cJ
    @13
    @23
    wceq
    #
    @14
    @25
    @16
    @27
    @8
    @13
    @23
    cD
    sseq2
    @39
    @15
    @26
    c0
    @13
    @23
    @7
    ineq2
    eqeq1d
    3anbi23d
    rspcev
    syl13anc
    vx
    cC
    cD
    cJ
    nrmsep2
    reximddv
end
