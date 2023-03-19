include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "prmssnn.mm"
include "nnssre.mm"
include "sstri.mm"
include "syl6ss.mm"
include "cfz.mm"
include "co.mm"
include "fzfid.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "cz.mm"
include "nnz.mm"
include "prmz.mm"
include "anim12i.mm"
include "3adant3.mm"
include "adantr.mm"
include "df-3an.mm"
include "sylibr.mm"
include "wi.mm"
include "nnre.mm"
include "sseli.mm"
include "ltle.mm"
include "syl2an.mm"
include "anim1d.mm"
include "ex.mm"
include "imp32.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "simp2.mm"
include "prmnn.mm"
include "nnred.mm"
include "leidd.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3adant1.mm"
include "ne0i.mm"
include "syl.mm"
include "wb.mm"
include "sseq1.mm"
include "eleq1.mm"
include "neeq1.mm"
include "3anbi123d.mm"
include "ax-mp.mm"
include "syl3anbrc.mm"
include "fiminre.mm"

theorem prmgaplem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cN: class N
  let vp: setvar p
  let vi: setvar i
  assume prmgaplem4.a: |- A = { p e. Prime | ( N < p /\ p <_ P ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint N p
  disjoint P p
  disjoint N i
  disjoint i p
  disjoint P i
  assert |- ( ( N e. NN /\ P e. Prime /\ N < P ) -> E. x e. A A. y e. A x <_ y )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    #
    cN
    cP
    clt
    wbr
    #
    w3a
    #
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    vx
    cv
    vy
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cA
    wrex
    @3
    cN
    vp
    cv
    #
    clt
    wbr
    #
    @8
    cP
    cle
    wbr
    #
    wa
    #
    vp
    cprime
    crab
    #
    cr
    wss
    #
    @12
    cfn
    wcel
    #
    @12
    c0
    wne
    #
    @7
    @3
    @12
    cprime
    cr
    @12
    cprime
    wss
    @3
    @11
    vp
    cprime
    ssrab2
    a1i
    cprime
    cn
    cr
    prmssnn
    nnssre
    sstri
    #
    syl6ss
    @3
    cN
    cP
    cfz
    co
    #
    cfn
    wcel
    @12
    @17
    wss
    @14
    @3
    cN
    cP
    fzfid
    @3
    vi
    @12
    @17
    vi
    cv
    #
    @12
    wcel
    @18
    cprime
    wcel
    #
    cN
    @18
    clt
    wbr
    #
    @18
    cP
    cle
    wbr
    #
    wa
    #
    wa
    #
    @3
    @18
    @17
    wcel
    #
    @11
    @22
    vp
    @18
    cprime
    @8
    @18
    wceq
    @9
    @20
    @10
    @21
    @8
    @18
    cN
    clt
    breq2
    @8
    @18
    cP
    cle
    breq1
    anbi12d
    elrab
    @3
    @23
    @24
    @3
    @23
    wa
    #
    cN
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @18
    cz
    wcel
    #
    w3a
    #
    cN
    @18
    cle
    wbr
    #
    @21
    wa
    #
    @24
    @25
    @26
    @27
    wa
    #
    @28
    wa
    @29
    @3
    @32
    @23
    @28
    @0
    @1
    @32
    @2
    @0
    @26
    @1
    @27
    cN
    nnz
    cP
    prmz
    anim12i
    3adant3
    @19
    @28
    @22
    @18
    prmz
    adantr
    anim12i
    @26
    @27
    @28
    df-3an
    sylibr
    @3
    @19
    @22
    @31
    @0
    @1
    @19
    @22
    @31
    wi
    #
    wi
    @2
    @0
    @1
    wa
    #
    @19
    @33
    @34
    @19
    wa
    @20
    @30
    @21
    @34
    cN
    cr
    wcel
    #
    @18
    cr
    wcel
    @20
    @30
    wi
    @19
    @0
    @35
    @1
    cN
    nnre
    adantr
    cprime
    cr
    @18
    @16
    sseli
    cN
    @18
    ltle
    syl2an
    anim1d
    ex
    3adant3
    imp32
    @18
    cN
    cP
    elfz2
    sylanbrc
    ex
    syl5bi
    ssrdv
    @17
    @12
    ssfi
    syl2anc
    @3
    cP
    @12
    wcel
    #
    @15
    @3
    @1
    @2
    cP
    cP
    cle
    wbr
    #
    wa
    #
    @36
    @0
    @1
    @2
    simp2
    @1
    @2
    @38
    @0
    @1
    @2
    wa
    @37
    @2
    @1
    @37
    @2
    @1
    cP
    @1
    cP
    cP
    prmnn
    nnred
    leidd
    anim1i
    ancomd
    3adant1
    @11
    @38
    vp
    cP
    cprime
    @8
    cP
    wceq
    @9
    @2
    @10
    @37
    @8
    cP
    cN
    clt
    breq2
    @8
    cP
    cP
    cle
    breq1
    anbi12d
    elrab
    sylanbrc
    @12
    cP
    ne0i
    syl
    cA
    @12
    wceq
    #
    @7
    @13
    @14
    @15
    w3a
    wb
    prmgaplem4.a
    @39
    @4
    @13
    @5
    @14
    @6
    @15
    cA
    @12
    cr
    sseq1
    cA
    @12
    cfn
    eleq1
    cA
    @12
    c0
    neeq1
    3anbi123d
    ax-mp
    syl3anbrc
    vx
    vy
    cA
    fiminre
    syl
end
