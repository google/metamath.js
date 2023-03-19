include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "cdif.mm"
include "cint.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "csuc.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wss.mm"
include "difss.mm"
include "ackbij1lem11.mm"
include "mpan2.mm"
include "con0.mm"
include "c0.mm"
include "wne.mm"
include "omsson.mm"
include "sstri.mm"
include "wn.mm"
include "ominf.mm"
include "inss2.mm"
include "sseli.mm"
include "difinf.mm"
include "sylancr.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "syl.mm"
include "onint.mm"
include "eldifad.mm"
include "ackbij1lem4.mm"
include "ackbij1lem6.mm"
include "syl2anc.mm"
include "coa.mm"
include "co.mm"
include "eldifbd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "ssdisj.mm"
include "ackbij1lem9.mm"
include "syl3anc.mm"
include "ackbij1lem14.mm"
include "oveq2d.mm"
include "ackbij1lem10.mm"
include "ffvelrni.mm"
include "ackbij1lem3.mm"
include "nnasuc.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "uncom.mm"
include "wa.mm"
include "wo.mm"
include "onnmin.mm"
include "mpan.mm"
include "con2i.mm"
include "adantl.mm"
include "word.mm"
include "ordom.mm"
include "ordelss.mm"
include "sselda.mm"
include "eldif.mm"
include "simplbi2.mm"
include "orrd.mm"
include "orcomd.mm"
include "orel1.mm"
include "sylc.mm"
include "ex.mm"
include "ssrdv.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "suceq.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"

theorem ackbij1lem18
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F b
  disjoint F x
  disjoint F y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. ( ~P _om i^i Fin ) -> E. b e. ( ~P _om i^i Fin ) ( F ` b ) = suc ( F ` A ) )

  proof
    cA
    com
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    cA
    com
    cA
    cdif
    #
    cint
    #
    cdif
    #
    @4
    csn
    #
    cun
    #
    @1
    wcel
    #
    @7
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    csuc
    #
    wceq
    #
    vb
    cv
    #
    cF
    cfv
    #
    @11
    wceq
    #
    vb
    @1
    wrex
    @2
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    @8
    @2
    @5
    cA
    wss
    #
    @16
    cA
    @4
    difss
    #
    vx
    vy
    cA
    @5
    cF
    ackbij.f
    ackbij1lem11
    mpan2
    #
    @2
    @4
    com
    wcel
    #
    @17
    @2
    @4
    com
    cA
    @2
    @3
    con0
    wss
    #
    @3
    c0
    wne
    #
    @4
    @3
    wcel
    @3
    com
    con0
    com
    cA
    difss
    omsson
    sstri
    #
    @2
    @3
    cfn
    wcel
    #
    wn
    #
    @23
    @2
    com
    cfn
    wcel
    wn
    cA
    cfn
    wcel
    @26
    ominf
    @1
    cfn
    cA
    @0
    cfn
    inss2
    sseli
    com
    cA
    difinf
    sylancr
    @25
    @3
    c0
    @3
    c0
    wceq
    @25
    c0
    cfn
    wcel
    0fin
    @3
    c0
    cfn
    eleq1
    mpbiri
    necon3bi
    syl
    @3
    onint
    sylancr
    #
    eldifad
    #
    @4
    ackbij1lem4
    syl
    #
    @5
    @6
    ackbij1lem6
    syl2anc
    @2
    @9
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    coa
    co
    #
    @30
    @4
    cF
    cfv
    #
    csuc
    #
    coa
    co
    #
    @11
    @2
    @16
    @17
    @5
    @6
    cin
    c0
    wceq
    #
    @9
    @32
    wceq
    @20
    @29
    @2
    @18
    cA
    @6
    cin
    c0
    wceq
    #
    @36
    @19
    @2
    @4
    cA
    wcel
    wn
    @37
    @2
    @4
    com
    cA
    @27
    eldifbd
    cA
    @4
    disjsn
    sylibr
    @5
    cA
    @6
    ssdisj
    sylancr
    vx
    vy
    @5
    @6
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    @2
    @31
    @34
    @30
    coa
    @2
    @21
    @31
    @34
    wceq
    @28
    vx
    vy
    @4
    cF
    ackbij.f
    ackbij1lem14
    syl
    oveq2d
    @2
    @35
    @30
    @33
    coa
    co
    #
    csuc
    #
    @11
    @2
    @30
    com
    wcel
    #
    @33
    com
    wcel
    #
    @35
    @39
    wceq
    @2
    @16
    @40
    @20
    @1
    com
    @5
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    #
    ffvelrni
    syl
    @2
    @4
    @1
    wcel
    #
    @41
    @2
    @21
    @43
    @28
    @4
    ackbij1lem3
    syl
    #
    @1
    com
    @4
    cF
    @42
    ffvelrni
    syl
    @30
    @33
    nnasuc
    syl2anc
    @2
    @38
    @10
    wceq
    @39
    @11
    wceq
    @2
    @5
    @4
    cun
    #
    cF
    cfv
    #
    @38
    @10
    @2
    @16
    @43
    @5
    @4
    cin
    #
    c0
    wceq
    #
    @46
    @38
    wceq
    @20
    @44
    @48
    @2
    @47
    @4
    @5
    cin
    c0
    @5
    @4
    incom
    @4
    cA
    disjdif
    eqtri
    a1i
    vx
    vy
    @5
    @4
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    @2
    @45
    cA
    cF
    @2
    @45
    @4
    @5
    cun
    #
    cA
    @5
    @4
    uncom
    @2
    @4
    cA
    wss
    @49
    cA
    wceq
    @2
    va
    @4
    cA
    @2
    va
    cv
    #
    @4
    wcel
    #
    @50
    cA
    wcel
    #
    @2
    @51
    wa
    #
    @50
    @3
    wcel
    #
    wn
    #
    @54
    @52
    wo
    #
    @52
    @51
    @55
    @2
    @54
    @51
    @22
    @54
    @51
    wn
    @24
    @3
    @50
    onnmin
    mpan
    con2i
    adantl
    @53
    @50
    com
    wcel
    #
    @56
    @2
    @4
    com
    @50
    @2
    com
    word
    @21
    @4
    com
    wss
    ordom
    @28
    com
    @4
    ordelss
    sylancr
    sselda
    @57
    @52
    @54
    @57
    @52
    @54
    @54
    @57
    @52
    wn
    @50
    com
    cA
    eldif
    simplbi2
    orrd
    orcomd
    syl
    @54
    @52
    orel1
    sylc
    ex
    ssrdv
    @4
    cA
    undif
    sylib
    syl5eq
    fveq2d
    eqtr3d
    @38
    @10
    suceq
    syl
    eqtrd
    3eqtrd
    @15
    @12
    vb
    @7
    @1
    @13
    @7
    wceq
    @14
    @9
    @11
    @13
    @7
    cF
    fveq2
    eqeq1d
    rspcev
    syl2anc
end
