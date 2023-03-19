include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpc.mm"
include "co.mm"
include "cprime.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cn0.mm"
include "pccl.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "simpr.mm"
include "simpl.mm"
include "oveq1.mm"
include "pcmpt.mm"
include "iftrue.mm"
include "wn.mm"
include "iffalse.mm"
include "cdvds.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "dvdsle.mm"
include "sylan.mm"
include "con3dimp.mm"
include "wb.mm"
include "pceq0.mm"
include "adantr.mm"
include "mpbird.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"
include "eqtrd.mm"
include "wf.mm"
include "pcmptcl.mm"
include "simprd.mm"
include "ffvelrn.mm"
include "mpancom.mm"
include "nnnn0d.mm"
include "nnnn0.mm"
include "pc11.mm"
include "syl2anc.mm"

theorem pcprod
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vp: setvar p
  assume pcprod.1: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ ( n pCnt N ) ) , 1 ) )

  disjoint N n
  disjoint F p
  disjoint n p
  disjoint N p
  assert |- ( N e. NN -> ( seq 1 ( x. , F ) ` N ) = N )

  proof
    cN
    cn
    wcel
    #
    cN
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cN
    wceq
    #
    vp
    cv
    #
    @2
    cpc
    co
    #
    @4
    cN
    cpc
    co
    #
    wceq
    #
    vp
    cprime
    wral
    #
    @0
    @7
    vp
    cprime
    @4
    cprime
    wcel
    #
    @0
    @7
    @9
    @0
    wa
    #
    @5
    @4
    cN
    cle
    wbr
    #
    @6
    cc0
    cif
    #
    @6
    @10
    vn
    cv
    #
    cN
    cpc
    co
    #
    @6
    @4
    vn
    cF
    cN
    pcprod.1
    @0
    @14
    cn0
    wcel
    #
    vn
    cprime
    wral
    @9
    @0
    @15
    vn
    cprime
    @13
    cprime
    wcel
    @0
    @15
    @13
    cN
    pccl
    ancoms
    ralrimiva
    #
    adantl
    @9
    @0
    simpr
    @9
    @0
    simpl
    @13
    @4
    cN
    cpc
    oveq1
    pcmpt
    @10
    @11
    @12
    @6
    wceq
    #
    @11
    @17
    @10
    @11
    @6
    cc0
    iftrue
    adantl
    @10
    @11
    wn
    #
    wa
    #
    @12
    cc0
    @6
    @18
    @12
    cc0
    wceq
    @10
    @11
    @6
    cc0
    iffalse
    adantl
    @19
    @6
    cc0
    wceq
    #
    @4
    cN
    cdvds
    wbr
    #
    wn
    #
    @10
    @21
    @11
    @9
    @4
    cz
    wcel
    @0
    @21
    @11
    wi
    @4
    prmz
    @4
    cN
    dvdsle
    sylan
    con3dimp
    @10
    @20
    @22
    wb
    @18
    @4
    cN
    pceq0
    adantr
    mpbird
    eqtr4d
    pm2.61dan
    eqtrd
    ancoms
    ralrimiva
    @0
    @2
    cn0
    wcel
    cN
    cn0
    wcel
    @3
    @8
    wb
    @0
    @2
    cn
    cn
    @1
    wf
    #
    @0
    @2
    cn
    wcel
    @0
    cn
    cn
    cF
    wf
    @23
    @0
    @14
    vn
    cF
    pcprod.1
    @16
    pcmptcl
    simprd
    cn
    cn
    cN
    @1
    ffvelrn
    mpancom
    nnnn0d
    cN
    nnnn0
    @2
    cN
    vp
    pc11
    syl2anc
    mpbird
end
