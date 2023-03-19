include "cpnrm.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "cdif.mm"
include "cv.mm"
include "crn.mm"
include "cint.mm"
include "wceq.mm"
include "ccld.mm"
include "cfv.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "ctop.mm"
include "pnrmtop.mm"
include "eqid.mm"
include "opncld.mm"
include "sylan.mm"
include "pnrmcld.mm"
include "syldan.mm"
include "cmpt.mm"
include "wf.mm"
include "ad2antrr.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "fvex.mm"
include "nnex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ciun.mm"
include "ciin.mm"
include "iundif2.mm"
include "wfn.mm"
include "ffn.mm"
include "fniinfv.mm"
include "3syl.mm"
include "difeq2d.mm"
include "syl5eq.mm"
include "cab.mm"
include "cvv.mm"
include "wral.mm"
include "uniexg.mm"
include "difexg.mm"
include "syl.mm"
include "ralrimivw.mm"
include "adantr.mm"
include "dfiun2g.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "eqtr3d.mm"
include "rneq.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ad2ant2r.mm"
include "difeq2.mm"
include "eqcomd.mm"
include "wss.mm"
include "elssuni.mm"
include "dfss4.mm"
include "sylib.mm"
include "sylan9eqr.mm"
include "ad2ant2l.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "rexlimddv.mm"

theorem pnrmopn
  let cA: class A
  let vf: setvar f
  let cJ: class J
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y

  disjoint A f
  disjoint J f
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
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
  assert |- ( ( J e. PNrm /\ A e. J ) -> E. f e. ( ( Clsd ` J ) ^m NN ) A = U. ran f )

  proof
    cJ
    cpnrm
    wcel
    #
    cA
    cJ
    wcel
    #
    wa
    #
    cJ
    cuni
    #
    cA
    cdif
    #
    vg
    cv
    #
    crn
    cint
    #
    wceq
    #
    cA
    vf
    cv
    #
    crn
    #
    cuni
    #
    wceq
    #
    vf
    cJ
    ccld
    cfv
    #
    cn
    cmap
    co
    #
    wrex
    #
    vg
    cJ
    cn
    cmap
    co
    #
    @0
    @1
    @4
    @12
    wcel
    #
    @7
    vg
    @15
    wrex
    @0
    cJ
    ctop
    wcel
    #
    @1
    @16
    cJ
    pnrmtop
    #
    cA
    cJ
    @3
    @3
    eqid
    #
    opncld
    sylan
    @4
    vg
    cJ
    pnrmcld
    syldan
    @2
    @5
    @15
    wcel
    #
    @7
    wa
    wa
    #
    @3
    @6
    cdif
    #
    @10
    wceq
    #
    vf
    @13
    wrex
    #
    @14
    @0
    @20
    @24
    @1
    @7
    @0
    @20
    wa
    #
    vx
    cn
    @3
    vx
    cv
    #
    @5
    cfv
    #
    cdif
    #
    cmpt
    #
    @13
    wcel
    #
    @22
    @29
    crn
    #
    cuni
    #
    wceq
    #
    @24
    @25
    cn
    @12
    @29
    wf
    @30
    @25
    vx
    cn
    @28
    @12
    @29
    @25
    @26
    cn
    wcel
    #
    wa
    @17
    @27
    cJ
    wcel
    @28
    @12
    wcel
    @0
    @17
    @20
    @34
    @18
    ad2antrr
    @25
    cn
    cJ
    @26
    @5
    @20
    cn
    cJ
    @5
    wf
    #
    @0
    @5
    cJ
    cn
    elmapi
    adantl
    #
    ffvelrnda
    @27
    cJ
    @3
    @19
    opncld
    syl2anc
    @29
    eqid
    #
    fmptd
    @12
    cn
    @29
    cJ
    ccld
    fvex
    nnex
    elmap
    sylibr
    @25
    vx
    cn
    @28
    ciun
    #
    @22
    @32
    @25
    @38
    @3
    vx
    cn
    @27
    ciin
    #
    cdif
    @22
    vx
    cn
    @3
    @27
    iundif2
    @25
    @39
    @6
    @3
    @25
    @35
    @5
    cn
    wfn
    @39
    @6
    wceq
    @36
    cn
    cJ
    @5
    ffn
    vx
    cn
    @5
    fniinfv
    3syl
    difeq2d
    syl5eq
    @25
    @38
    @8
    @28
    wceq
    vx
    cn
    wrex
    vf
    cab
    #
    cuni
    #
    @32
    @25
    @28
    cvv
    wcel
    #
    vx
    cn
    wral
    #
    @38
    @41
    wceq
    @0
    @43
    @20
    @0
    @42
    vx
    cn
    @0
    @3
    cvv
    wcel
    @42
    cJ
    cpnrm
    uniexg
    @3
    @27
    cvv
    difexg
    syl
    ralrimivw
    adantr
    vx
    vf
    cn
    @28
    cvv
    dfiun2g
    syl
    @31
    @40
    vx
    vf
    cn
    @28
    @29
    @37
    rnmpt
    unieqi
    syl6eqr
    eqtr3d
    @23
    @33
    vf
    @29
    @13
    @8
    @29
    wceq
    #
    @10
    @32
    @22
    @44
    @9
    @31
    @8
    @29
    rneq
    unieqd
    eqeq2d
    rspcev
    syl2anc
    ad2ant2r
    @21
    @23
    @11
    vf
    @13
    @21
    @22
    cA
    @10
    @1
    @7
    @22
    cA
    wceq
    @0
    @20
    @7
    @1
    @22
    @3
    @4
    cdif
    #
    cA
    @7
    @45
    @22
    @4
    @6
    @3
    difeq2
    eqcomd
    @1
    cA
    @3
    wss
    @45
    cA
    wceq
    cA
    cJ
    elssuni
    cA
    @3
    dfss4
    sylib
    sylan9eqr
    ad2ant2l
    eqeq1d
    rexbidv
    mpbid
    rexlimddv
end
