include "creg.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wn.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wrex.mm"
include "ccl.mm"
include "cdif.mm"
include "ctop.mm"
include "regtop.mm"
include "ad2antrr.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ad2antrl.mm"
include "clscld.mm"
include "syl2anc.mm"
include "cldopn.mm"
include "syl.mm"
include "simprrr.mm"
include "wb.mm"
include "clsss3.mm"
include "simplr1.mm"
include "cldss.mm"
include "ssconb.mm"
include "mpbid.mm"
include "simprrl.mm"
include "sscls.mm"
include "sslin.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "sseq0.mm"
include "sylancl.mm"
include "sseq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "eldifd.mm"
include "regsep.mm"
include "syl3anc.mm"
include "reximddv.mm"
include "rexcom.mm"
include "sylib.mm"

theorem regsep2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let cB: class B
  assume t1sep.1: |- X = U. J

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint o x
  disjoint o y
  disjoint A o
  disjoint B o
  disjoint B y
  disjoint J o
  disjoint X o
  assert |- ( ( J e. Reg /\ ( C e. ( Clsd ` J ) /\ A e. X /\ -. A e. C ) ) -> E. x e. J E. y e. J ( C C_ x /\ A e. y /\ ( x i^i y ) = (/) ) )

  proof
    cJ
    creg
    wcel
    #
    cC
    cJ
    ccld
    cfv
    #
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cC
    wcel
    wn
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
    cA
    vy
    cv
    #
    wcel
    #
    @7
    @9
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vx
    cJ
    wrex
    #
    vy
    cJ
    wrex
    @13
    vy
    cJ
    wrex
    vx
    cJ
    wrex
    @6
    @10
    @9
    cJ
    ccl
    cfv
    cfv
    #
    cX
    cC
    cdif
    #
    wss
    #
    wa
    #
    @14
    vy
    cJ
    @6
    @9
    cJ
    wcel
    #
    @18
    wa
    #
    wa
    #
    cX
    @15
    cdif
    #
    cJ
    wcel
    #
    cC
    @22
    wss
    #
    @10
    @22
    @9
    cin
    #
    c0
    wceq
    #
    @14
    @21
    @15
    @1
    wcel
    #
    @23
    @21
    cJ
    ctop
    wcel
    #
    @9
    cX
    wss
    #
    @27
    @0
    @28
    @5
    @20
    cJ
    regtop
    ad2antrr
    #
    @19
    @29
    @6
    @18
    @19
    @9
    cJ
    cuni
    cX
    @9
    cJ
    elssuni
    t1sep.1
    syl6sseqr
    ad2antrl
    #
    @9
    cJ
    cX
    t1sep.1
    clscld
    syl2anc
    @15
    cJ
    cX
    t1sep.1
    cldopn
    syl
    @21
    @17
    @24
    @6
    @19
    @10
    @17
    simprrr
    @21
    @15
    cX
    wss
    #
    cC
    cX
    wss
    #
    @17
    @24
    wb
    @21
    @28
    @29
    @32
    @30
    @31
    @9
    cJ
    cX
    t1sep.1
    clsss3
    syl2anc
    @21
    @2
    @33
    @2
    @3
    @4
    @0
    @20
    simplr1
    cC
    cJ
    cX
    t1sep.1
    cldss
    syl
    @15
    cC
    cX
    ssconb
    syl2anc
    mpbid
    @6
    @19
    @10
    @17
    simprrl
    @21
    @25
    @22
    @15
    cin
    #
    wss
    #
    @34
    c0
    wceq
    @26
    @21
    @9
    @15
    wss
    #
    @35
    @21
    @28
    @29
    @36
    @30
    @31
    @9
    cJ
    cX
    t1sep.1
    sscls
    syl2anc
    @9
    @15
    @22
    sslin
    syl
    @34
    @15
    @22
    cin
    c0
    @22
    @15
    incom
    @15
    cX
    disjdif
    eqtri
    @25
    @34
    sseq0
    sylancl
    @13
    @24
    @10
    @26
    w3a
    vx
    @22
    cJ
    @7
    @22
    wceq
    #
    @8
    @24
    @12
    @26
    @10
    @7
    @22
    cC
    sseq2
    @37
    @11
    @25
    c0
    @7
    @22
    @9
    ineq1
    eqeq1d
    3anbi13d
    rspcev
    syl13anc
    @6
    @0
    @16
    cJ
    wcel
    #
    cA
    @16
    wcel
    @18
    vy
    cJ
    wrex
    @0
    @5
    simpl
    @6
    @2
    @38
    @0
    @2
    @3
    @4
    simpr1
    cC
    cJ
    cX
    t1sep.1
    cldopn
    syl
    @6
    cA
    cX
    cC
    @0
    @2
    @3
    @4
    simpr2
    @0
    @2
    @3
    @4
    simpr3
    eldifd
    vy
    cA
    @16
    cJ
    regsep
    syl3anc
    reximddv
    @13
    vy
    vx
    cJ
    cJ
    rexcom
    sylib
end
