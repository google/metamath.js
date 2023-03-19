include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cvol.mm"
include "wa.mm"
include "cr.mm"
include "crn.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "wfn.mm"
include "wf.mm"
include "i1ff.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "i1f0rn.mm"
include "ad2antrr.mm"
include "ifcld.mm"
include "fmptd.mm"
include "wss.mm"
include "frn.mm"
include "fssd.mm"
include "cfn.mm"
include "i1frn.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "wne.mm"
include "wn.mm"
include "eldifsni.mm"
include "ad2antlr.mm"
include "necomd.mm"
include "iffalse.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "necon4bd.mm"
include "pm4.71rd.mm"
include "bitrd.mm"
include "iftrue.mm"
include "pm5.32i.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "an12.mm"
include "wb.mm"
include "fniniseg.mm"
include "anbi2d.mm"
include "3bitr4d.mm"
include "elin.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "simplr.mm"
include "i1fima.mm"
include "inmbl.mm"
include "eqeltrd.mm"
include "covol.mm"
include "fveq2d.mm"
include "mblvol.mm"
include "eqtrd.mm"
include "inss2.mm"
include "a1i.mm"
include "mblss.mm"
include "i1fima2sn.mm"
include "adantlr.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "i1fd.mm"

theorem i1fres
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  assume i1fres.1: |- G = ( x e. RR |-> if ( x e. A , ( F ` x ) , 0 ) )

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  assert |- ( ( F e. dom S.1 /\ A e. dom vol ) -> G e. dom S.1 )

  proof
    cF
    citg1
    cdm
    wcel
    #
    cA
    cvol
    cdm
    #
    wcel
    #
    wa
    #
    vy
    cG
    @3
    cr
    cF
    crn
    #
    cr
    cG
    @3
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    @5
    cF
    cfv
    #
    cc0
    cif
    #
    @4
    cG
    @3
    @5
    cr
    wcel
    #
    wa
    @6
    @7
    cc0
    @4
    @3
    cF
    cr
    wfn
    #
    @9
    @7
    @4
    wcel
    @3
    cr
    cr
    cF
    wf
    #
    @10
    @0
    @11
    @2
    cF
    i1ff
    adantr
    #
    cr
    cr
    cF
    ffn
    syl
    #
    cr
    @5
    cF
    fnfvelrn
    sylan
    @0
    cc0
    @4
    wcel
    @2
    @9
    cF
    i1f0rn
    ad2antrr
    ifcld
    i1fres.1
    fmptd
    #
    @3
    @11
    @4
    cr
    wss
    @12
    cr
    cr
    cF
    frn
    syl
    fssd
    @3
    @4
    cfn
    wcel
    #
    cG
    crn
    #
    @4
    wss
    #
    @16
    cfn
    wcel
    @0
    @15
    @2
    cF
    i1frn
    adantr
    @3
    cr
    @4
    cG
    wf
    #
    @17
    @14
    cr
    @4
    cG
    frn
    syl
    @4
    @16
    ssfi
    syl2anc
    @3
    vy
    cv
    #
    @16
    cc0
    csn
    cdif
    wcel
    #
    wa
    #
    cG
    ccnv
    @19
    csn
    #
    cima
    #
    cA
    cF
    ccnv
    @22
    cima
    #
    cin
    #
    @1
    @21
    vz
    @23
    @25
    @21
    vz
    cv
    #
    @23
    wcel
    #
    @26
    cA
    wcel
    #
    @26
    @24
    wcel
    #
    wa
    #
    @26
    @25
    wcel
    @21
    @26
    cr
    wcel
    #
    @26
    cG
    cfv
    #
    @19
    wceq
    #
    wa
    #
    @28
    @31
    @26
    cF
    cfv
    #
    @19
    wceq
    #
    wa
    #
    wa
    #
    @27
    @30
    @21
    @34
    @31
    @28
    @36
    wa
    #
    wa
    @38
    @21
    @31
    @33
    @39
    @21
    @31
    wa
    #
    @33
    @28
    @28
    @35
    cc0
    cif
    #
    @19
    wceq
    #
    wa
    #
    @39
    @40
    @33
    @42
    @43
    @40
    @32
    @41
    @19
    @31
    @32
    @41
    wceq
    @21
    vx
    @26
    @8
    @41
    cr
    cG
    @5
    @26
    wceq
    @6
    @28
    @7
    @35
    cc0
    @5
    @26
    cA
    eleq1
    @5
    @26
    cF
    fveq2
    ifbieq1d
    i1fres.1
    @28
    @35
    cc0
    @26
    cF
    fvex
    c0ex
    ifex
    fvmpt
    adantl
    eqeq1d
    @40
    @42
    @28
    @40
    @28
    @41
    @19
    @40
    @41
    @19
    wne
    @28
    wn
    #
    cc0
    @19
    wne
    @40
    @19
    cc0
    @20
    @19
    cc0
    wne
    @3
    @31
    @19
    @16
    cc0
    eldifsni
    ad2antlr
    necomd
    @44
    @41
    cc0
    @19
    @28
    @35
    cc0
    iffalse
    neeq1d
    syl5ibrcom
    necon4bd
    pm4.71rd
    bitrd
    @28
    @42
    @36
    @28
    @41
    @35
    @19
    @28
    @35
    cc0
    iftrue
    eqeq1d
    pm5.32i
    syl6bb
    pm5.32da
    @31
    @28
    @36
    an12
    syl6bb
    @21
    cG
    cr
    wfn
    #
    @27
    @34
    wb
    @3
    @45
    @20
    @3
    @18
    @45
    @14
    cr
    @4
    cG
    ffn
    syl
    adantr
    cr
    @19
    @26
    cG
    fniniseg
    syl
    @21
    @29
    @37
    @28
    @21
    @10
    @29
    @37
    wb
    @3
    @10
    @20
    @13
    adantr
    cr
    @19
    @26
    cF
    fniniseg
    syl
    anbi2d
    3bitr4d
    @26
    cA
    @24
    elin
    syl6bbr
    eqrdv
    #
    @21
    @2
    @24
    @1
    wcel
    #
    @25
    @1
    wcel
    #
    @0
    @2
    @20
    simplr
    @0
    @47
    @2
    @20
    @22
    cF
    i1fima
    ad2antrr
    #
    cA
    @24
    inmbl
    syl2anc
    #
    eqeltrd
    @21
    @23
    cvol
    cfv
    #
    @25
    covol
    cfv
    #
    cr
    @21
    @51
    @25
    cvol
    cfv
    #
    @52
    @21
    @23
    @25
    cvol
    @46
    fveq2d
    @21
    @48
    @53
    @52
    wceq
    @50
    @25
    mblvol
    syl
    eqtrd
    @21
    @25
    @24
    wss
    #
    @24
    cr
    wss
    #
    @24
    covol
    cfv
    #
    cr
    wcel
    @52
    cr
    wcel
    @54
    @21
    cA
    @24
    inss2
    a1i
    @21
    @47
    @55
    @49
    @24
    mblss
    syl
    @21
    @24
    cvol
    cfv
    #
    @56
    cr
    @21
    @47
    @57
    @56
    wceq
    @49
    @24
    mblvol
    syl
    @0
    @20
    @57
    cr
    wcel
    @2
    @19
    @16
    cF
    i1fima2sn
    adantlr
    eqeltrrd
    @25
    @24
    ovolsscl
    syl3anc
    eqeltrd
    i1fd
end
