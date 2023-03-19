include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "cdm.mm"
include "cres.mm"
include "cun.mm"
include "cin.mm"
include "wceq.mm"
include "funres.mm"
include "adantl.mm"
include "adantr.mm"
include "funsng.mm"
include "dmres.mm"
include "ineq1i.mm"
include "in32.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "0in.mm"
include "3eqtri.mm"
include "a1i.mm"
include "funun.mm"
include "syl21anc.mm"
include "difundir.mm"
include "resdifcom.mm"
include "wne.mm"
include "elex.mm"
include "anim12i.mm"
include "opnz.mm"
include "sylibr.mm"
include "disjsn2.mm"
include "disjdif2.mm"
include "3syl.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "funeqd.mm"
include "mpbird.mm"
include "wb.mm"
include "opex.mm"
include "setsvalg.mm"
include "sylan2.mm"
include "difeq1d.mm"

theorem setsfun0
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( ( G e. V /\ Fun ( G \ { (/) } ) ) /\ ( I e. U /\ E e. W ) ) -> Fun ( ( G sSet <. I , E >. ) \ { (/) } ) )

  proof
    cG
    cV
    wcel
    #
    cG
    c0
    csn
    #
    cdif
    #
    wfun
    #
    wa
    #
    cI
    cU
    wcel
    #
    cE
    cW
    wcel
    #
    wa
    #
    wa
    #
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    @1
    cdif
    #
    wfun
    #
    cG
    cvv
    @9
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @13
    cun
    #
    @1
    cdif
    #
    wfun
    #
    @8
    @19
    @2
    @15
    cres
    #
    @13
    cun
    #
    wfun
    #
    @8
    @20
    wfun
    #
    @13
    wfun
    #
    @20
    cdm
    #
    @14
    cin
    #
    c0
    wceq
    #
    @22
    @4
    @23
    @7
    @3
    @23
    @0
    @15
    @2
    funres
    adantl
    adantr
    @7
    @24
    @4
    cI
    cE
    cU
    cW
    funsng
    adantl
    @27
    @8
    @26
    @15
    @2
    cdm
    #
    cin
    #
    @14
    cin
    #
    c0
    @25
    @29
    @14
    @2
    @15
    dmres
    ineq1i
    @30
    @15
    @14
    cin
    #
    @28
    cin
    c0
    @28
    cin
    c0
    @15
    @28
    @14
    in32
    @31
    c0
    @28
    @31
    @14
    @15
    cin
    c0
    @15
    @14
    incom
    @14
    cvv
    disjdif
    eqtri
    ineq1i
    @28
    0in
    3eqtri
    eqtri
    a1i
    @20
    @13
    funun
    syl21anc
    @8
    @18
    @21
    @8
    @18
    @16
    @1
    cdif
    #
    @13
    @1
    cdif
    #
    cun
    @21
    @16
    @13
    @1
    difundir
    @8
    @32
    @20
    @33
    @13
    @32
    @20
    wceq
    @8
    cG
    @15
    @1
    resdifcom
    a1i
    @8
    @9
    c0
    wne
    #
    @13
    @1
    cin
    c0
    wceq
    @33
    @13
    wceq
    @7
    @34
    @4
    @7
    cI
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    wa
    @34
    @5
    @35
    @6
    @36
    cI
    cU
    elex
    cE
    cW
    elex
    anim12i
    cI
    cE
    opnz
    sylibr
    adantl
    @9
    c0
    disjsn2
    @13
    @1
    disjdif2
    3syl
    uneq12d
    syl5eq
    funeqd
    mpbird
    @4
    @12
    @19
    wb
    @7
    @4
    @11
    @18
    @4
    @10
    @17
    @1
    @3
    @0
    @9
    cvv
    wcel
    #
    @10
    @17
    wceq
    @37
    @3
    cI
    cE
    opex
    a1i
    @9
    cG
    cV
    cvv
    setsvalg
    sylan2
    difeq1d
    funeqd
    adantr
    mpbird
end
