include "wcel.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cdif.mm"
include "cfn.mm"
include "cpw.mm"
include "crab.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cint.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cfil.mm"
include "wn.mm"
include "ominf.mm"
include "domfi.mm"
include "expcom.mm"
include "mtoi.mm"
include "cfinfil.mm"
include "syl3an3.mm"
include "filssufil.mm"
include "syl.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "3adant3.mm"
include "0fin.mm"
include "a1i.mm"
include "difeq2.mm"
include "difid.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ssel.mm"
include "syl5com.mm"
include "intss.mm"
include "csn.mm"
include "neldifsn.mm"
include "elinti.mm"
include "simp2.mm"
include "ssdifssd.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "snfi.mm"
include "wi.mm"
include "eldif.mm"
include "notbii.mm"
include "iman.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "pm3.35.mm"
include "sylbi.mm"
include "ssriv.mm"
include "ssfi.mm"
include "mp2an.mm"
include "nsyl3.mm"
include "eq0rdv.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "ss0.mm"
include "syl6.mm"
include "jcad.mm"
include "reximdv.mm"
include "mpd.mm"

theorem ufinffr
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cX: class X
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint B f
  disjoint X f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint X x
  disjoint X y
  assert |- ( ( X e. B /\ A C_ X /\ _om ~<_ A ) -> E. f e. ( UFil ` X ) ( A e. f /\ |^| f = (/) ) )

  proof
    cX
    cB
    wcel
    #
    cA
    cX
    wss
    #
    com
    cA
    cdom
    wbr
    #
    w3a
    #
    cA
    vx
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    vf
    cv
    #
    wss
    #
    vf
    cX
    cufil
    cfv
    #
    wrex
    #
    cA
    @9
    wcel
    #
    @9
    cint
    #
    c0
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    @3
    @8
    cX
    cfil
    cfv
    wcel
    #
    @12
    @2
    @0
    @1
    cA
    cfn
    wcel
    #
    wn
    @17
    @2
    @18
    com
    cfn
    wcel
    #
    ominf
    @18
    @2
    @19
    cA
    com
    domfi
    expcom
    mtoi
    vx
    cA
    cB
    cX
    cfinfil
    syl3an3
    vf
    @8
    cX
    filssufil
    syl
    @3
    @10
    @16
    vf
    @11
    @3
    @10
    @13
    @15
    @3
    cA
    @8
    wcel
    #
    @10
    @13
    @3
    cA
    @7
    wcel
    #
    c0
    cfn
    wcel
    #
    @20
    @0
    @1
    @21
    @2
    @0
    @21
    @1
    cA
    cX
    cB
    elpw2g
    biimpar
    3adant3
    @22
    @3
    0fin
    a1i
    @6
    @22
    vx
    cA
    @7
    @4
    cA
    wceq
    #
    @5
    c0
    cfn
    @23
    @5
    cA
    cA
    cdif
    c0
    @4
    cA
    cA
    difeq2
    cA
    difid
    syl6eq
    eleq1d
    elrab
    sylanbrc
    @8
    @9
    cA
    ssel
    syl5com
    @3
    @10
    @14
    c0
    wss
    #
    @15
    @10
    @14
    @8
    cint
    #
    wss
    @3
    @24
    @8
    @9
    intss
    @3
    @25
    c0
    @14
    @3
    vy
    @25
    vy
    cv
    #
    @25
    wcel
    #
    cA
    @26
    csn
    #
    cdif
    #
    @8
    wcel
    #
    @3
    @27
    @30
    @26
    @29
    wcel
    @26
    cA
    neldifsn
    @26
    @8
    @29
    elinti
    mtoi
    @3
    @29
    @7
    wcel
    #
    cA
    @29
    cdif
    #
    cfn
    wcel
    #
    @30
    @3
    @31
    @29
    cX
    wss
    #
    @3
    cA
    cX
    @28
    @0
    @1
    @2
    simp2
    ssdifssd
    @0
    @1
    @31
    @34
    wb
    @2
    @29
    cX
    cB
    elpw2g
    3ad2ant1
    mpbird
    @33
    @3
    @28
    cfn
    wcel
    @32
    @28
    wss
    @33
    @26
    snfi
    vx
    @32
    @28
    @4
    @32
    wcel
    #
    @4
    cA
    wcel
    #
    @36
    @4
    @28
    wcel
    #
    wi
    #
    wa
    #
    @37
    @35
    @36
    @4
    @29
    wcel
    #
    wn
    #
    wa
    @39
    @4
    cA
    @29
    eldif
    @41
    @38
    @36
    @41
    @36
    @37
    wn
    wa
    #
    wn
    @38
    @40
    @42
    @4
    cA
    @28
    eldif
    notbii
    @36
    @37
    iman
    bitr4i
    anbi2i
    bitri
    @36
    @37
    pm3.35
    sylbi
    ssriv
    @28
    @32
    ssfi
    mp2an
    a1i
    @6
    @33
    vx
    @29
    @7
    @4
    @29
    wceq
    @5
    @32
    cfn
    @4
    @29
    cA
    difeq2
    eleq1d
    elrab
    sylanbrc
    nsyl3
    eq0rdv
    sseq2d
    syl5ib
    @14
    ss0
    syl6
    jcad
    reximdv
    mpd
end
