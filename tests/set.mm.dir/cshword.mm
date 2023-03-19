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
include "oveq12d.mm"
include "wrd0.mm"
include "ccatrid.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61ian.mm"

theorem cshword
  let cN: class N
  let cV: class V
  let cW: class W
  let vl: setvar l
  let vw: setvar w


  assert |- ( ( W e. Word V /\ N e. ZZ ) -> ( W cyclShift N ) = ( ( W substr <. ( N mod ( # ` W ) ) , ( # ` W ) >. ) ++ ( W substr <. 0 , ( N mod ( # ` W ) ) >. ) ) )

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
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    #
    @12
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
    @13
    wceq
    @1
    @18
    cW
    @15
    wfn
    #
    vl
    cn0
    wrex
    #
    @1
    @15
    cV
    cW
    wf
    #
    vl
    cn0
    wrex
    @20
    cV
    cW
    vl
    iswrd
    @21
    @19
    vl
    cn0
    @15
    cV
    cW
    ffn
    reximi
    sylbi
    @17
    @20
    vw
    cW
    @0
    @14
    cW
    wceq
    @16
    @19
    vl
    cn0
    @15
    @14
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
    @13
    @12
    wceq
    #
    @5
    @3
    wa
    #
    @13
    c0
    @12
    @5
    @13
    c0
    wceq
    @3
    @5
    c0
    @12
    iftrue
    adantr
    @23
    @12
    c0
    c0
    cconcat
    co
    #
    c0
    @5
    @12
    @24
    wceq
    @3
    @5
    @9
    c0
    @11
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
    @11
    c0
    @10
    csubstr
    co
    c0
    cW
    c0
    @10
    csubstr
    oveq1
    cc0
    @7
    swrd0
    syl6eq
    oveq12d
    adantr
    c0
    @0
    wcel
    @24
    c0
    wceq
    cV
    wrd0
    cV
    c0
    ccatrid
    ax-mp
    syl6req
    eqtrd
    @5
    wn
    @22
    @3
    @5
    c0
    @12
    iffalse
    adantr
    pm2.61ian
    eqtrd
end
