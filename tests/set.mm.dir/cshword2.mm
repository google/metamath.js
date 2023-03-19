include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cc0.mm"
include "cconcat.mm"
include "cif.mm"
include "cpfx.mm"
include "cv.mm"
include "cfzo.mm"
include "wfn.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "wf.mm"
include "iswrd.mm"
include "ffn.mm"
include "reximi.mm"
include "sylbi.mm"
include "fneq1.mm"
include "rexbidv.mm"
include "elabg.mm"
include "mpbird.mm"
include "cshfn.mm"
include "sylan.mm"
include "iftrue.mm"
include "adantr.mm"
include "oveq1.mm"
include "swrd0.mm"
include "syl6eq.mm"
include "pfx0.mm"
include "oveq12d.mm"
include "cvv.mm"
include "wrd0.mm"
include "ccatrid.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "simprl.mm"
include "simprr.mm"
include "cn.mm"
include "wne.mm"
include "df-ne.mm"
include "wi.mm"
include "lennncl.mm"
include "ex.mm"
include "syl5bir.mm"
include "impcom.mm"
include "zmodcld.mm"
include "pfxval.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "pm2.61ian.mm"

theorem cshword2
  let cN: class N
  let cV: class V
  let cW: class W
  let vl: setvar l
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( W cyclShift N ) = ( ( W substr <. ( N mod ( # ` W ) ) , ( # ` W ) >. ) ++ ( W prefix ( N mod ( # ` W ) ) ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cW
    cN
    ccsh
    co
    #
    cW
    c0
    wceq
    #
    c0
    cW
    cN
    cW
    chash
    cfv
    #
    cmo
    co
    #
    @6
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    @7
    cop
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    #
    @9
    cW
    @7
    cpfx
    co
    #
    cconcat
    co
    #
    @1
    cW
    vw
    cv
    #
    cc0
    vl
    cv
    cfzo
    co
    #
    wfn
    #
    vl
    cn0
    wrex
    #
    vw
    cab
    wcel
    #
    @2
    @4
    @12
    wceq
    @1
    @19
    cW
    @16
    wfn
    #
    vl
    cn0
    wrex
    #
    @1
    @16
    cV
    cW
    wf
    #
    vl
    cn0
    wrex
    @21
    cV
    cW
    vl
    iswrd
    @22
    @20
    vl
    cn0
    @16
    cV
    cW
    ffn
    reximi
    sylbi
    @18
    @21
    vw
    cW
    @0
    @15
    cW
    wceq
    @17
    @20
    vl
    cn0
    @16
    @15
    cW
    fneq1
    rexbidv
    elabg
    mpbird
    vw
    cN
    cW
    vl
    cshfn
    sylan
    @5
    @3
    @12
    @14
    wceq
    @5
    @3
    wa
    #
    @12
    c0
    @14
    @5
    @12
    c0
    wceq
    @3
    @5
    c0
    @11
    iftrue
    adantr
    @23
    @14
    c0
    c0
    cconcat
    co
    #
    c0
    @5
    @14
    @24
    wceq
    @3
    @5
    @9
    c0
    @13
    c0
    cconcat
    @5
    @9
    c0
    @8
    csubstr
    co
    c0
    cW
    c0
    @8
    csubstr
    oveq1
    @7
    @6
    swrd0
    syl6eq
    @5
    @13
    c0
    @7
    cpfx
    co
    c0
    cW
    c0
    @7
    cpfx
    oveq1
    @7
    pfx0
    syl6eq
    oveq12d
    adantr
    c0
    cvv
    cword
    wcel
    @24
    c0
    wceq
    cvv
    wrd0
    cvv
    c0
    ccatrid
    ax-mp
    syl6req
    eqtrd
    @5
    wn
    #
    @3
    wa
    #
    @12
    @11
    @14
    @25
    @12
    @11
    wceq
    @3
    @5
    c0
    @11
    iffalse
    adantr
    @26
    @10
    @13
    @9
    cconcat
    @26
    @13
    @10
    @26
    @1
    @7
    cn0
    wcel
    @13
    @10
    wceq
    @25
    @1
    @2
    simprl
    @26
    cN
    @6
    @25
    @1
    @2
    simprr
    @3
    @25
    @6
    cn
    wcel
    #
    @25
    cW
    c0
    wne
    #
    @3
    @27
    cW
    c0
    df-ne
    @1
    @28
    @27
    wi
    @2
    @1
    @28
    @27
    cV
    cW
    lennncl
    ex
    adantr
    syl5bir
    impcom
    zmodcld
    cW
    @7
    @0
    pfxval
    syl2anc
    eqcomd
    oveq2d
    eqtrd
    pm2.61ian
    eqtrd
end
