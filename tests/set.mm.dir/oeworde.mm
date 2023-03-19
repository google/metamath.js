include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "cdif.mm"
include "coe.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "id.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "0ss.mm"
include "a1i.mm"
include "wi.mm"
include "wa.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "adantl.mm"
include "eldifi.mm"
include "oecl.mm"
include "sylan.mm"
include "syl.mm"
include "ordsucsssuc.mm"
include "syl2anc.mm"
include "suceloni.mm"
include "syl2an.mm"
include "vex.mm"
include "sucid.mm"
include "oeordi.mm"
include "mpi.mm"
include "syl2anr.mm"
include "ordsucss.mm"
include "sylc.mm"
include "sstr2.mm"
include "syl5com.mm"
include "sylbid.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "dif20el.mm"
include "jca.mm"
include "ciun.mm"
include "ss2iun.mm"
include "cuni.mm"
include "limuni.mm"
include "uniiun.mm"
include "syl6eq.mm"
include "adantr.mm"
include "cvv.mm"
include "oelim.mm"
include "mpanlr1.mm"
include "anasss.mm"
include "an12s.mm"
include "syl5ibr.mm"
include "ex.mm"
include "syl5.mm"
include "tfinds3.mm"
include "impcom.mm"

theorem oeworde
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. ( On \ 2o ) /\ B e. On ) -> B C_ ( A ^o B ) )

  proof
    cB
    con0
    wcel
    cA
    con0
    c2o
    cdif
    wcel
    #
    cB
    cA
    cB
    coe
    co
    #
    wss
    #
    vx
    cv
    #
    cA
    @3
    coe
    co
    #
    wss
    #
    c0
    cA
    c0
    coe
    co
    #
    wss
    #
    vy
    cv
    #
    cA
    @8
    coe
    co
    #
    wss
    #
    @8
    csuc
    #
    cA
    @11
    coe
    co
    #
    wss
    #
    @2
    @0
    vx
    vy
    cB
    @3
    c0
    wceq
    #
    @3
    c0
    @4
    @6
    @14
    id
    @3
    c0
    cA
    coe
    oveq2
    sseq12d
    @3
    @8
    wceq
    #
    @3
    @8
    @4
    @9
    @15
    id
    @3
    @8
    cA
    coe
    oveq2
    sseq12d
    @3
    @11
    wceq
    #
    @3
    @11
    @4
    @12
    @16
    id
    @3
    @11
    cA
    coe
    oveq2
    sseq12d
    @3
    cB
    wceq
    #
    @3
    cB
    @4
    @1
    @17
    id
    @3
    cB
    cA
    coe
    oveq2
    sseq12d
    @7
    @0
    @6
    0ss
    a1i
    @0
    @8
    con0
    wcel
    #
    @10
    @13
    wi
    @0
    @18
    wa
    #
    @10
    @11
    @9
    csuc
    #
    wss
    #
    @13
    @19
    @8
    word
    #
    @9
    word
    #
    @10
    @21
    wb
    @18
    @22
    @0
    @8
    eloni
    adantl
    @19
    @9
    con0
    wcel
    #
    @23
    @0
    cA
    con0
    wcel
    #
    @18
    @24
    cA
    con0
    c2o
    eldifi
    #
    cA
    @8
    oecl
    sylan
    @9
    eloni
    syl
    @8
    @9
    ordsucsssuc
    syl2anc
    @19
    @20
    @12
    wss
    #
    @21
    @13
    @19
    @12
    word
    #
    @9
    @12
    wcel
    #
    @27
    @19
    @12
    con0
    wcel
    #
    @28
    @0
    @25
    @11
    con0
    wcel
    #
    @30
    @18
    @26
    @8
    suceloni
    #
    cA
    @11
    oecl
    syl2an
    @12
    eloni
    syl
    @18
    @31
    @0
    @29
    @0
    @32
    @0
    id
    @31
    @0
    wa
    @8
    @11
    wcel
    @29
    @8
    vy
    vex
    sucid
    @8
    @11
    cA
    oeordi
    mpi
    syl2anr
    @9
    @12
    ordsucss
    sylc
    @11
    @20
    @12
    sstr2
    syl5com
    sylbid
    expcom
    @0
    @25
    c0
    cA
    wcel
    #
    wa
    #
    @3
    wlim
    #
    @10
    vy
    @3
    wral
    #
    @5
    wi
    #
    @0
    @25
    @33
    @26
    cA
    dif20el
    jca
    @35
    @34
    @37
    @36
    @5
    @35
    @34
    wa
    #
    vy
    @3
    @8
    ciun
    #
    vy
    @3
    @9
    ciun
    #
    wss
    vy
    @3
    @8
    @9
    ss2iun
    @38
    @3
    @39
    @4
    @40
    @35
    @3
    @39
    wceq
    @34
    @35
    @3
    @3
    cuni
    @39
    @3
    limuni
    vy
    @3
    uniiun
    syl6eq
    adantr
    @25
    @35
    @33
    @4
    @40
    wceq
    #
    @25
    @35
    @33
    @41
    @25
    @3
    cvv
    wcel
    @35
    @33
    @41
    vx
    vex
    vy
    cA
    @3
    cvv
    oelim
    mpanlr1
    anasss
    an12s
    sseq12d
    syl5ibr
    ex
    syl5
    tfinds3
    impcom
end
