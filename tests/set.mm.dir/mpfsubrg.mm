include "wcel.mm"
include "ccrg.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "ces.mm"
include "co.mm"
include "cress.mm"
include "cmpl.mm"
include "cbs.mm"
include "cima.mm"
include "cmap.mm"
include "cpws.mm"
include "crn.mm"
include "crh.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "evlsrhm.mm"
include "rhmf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnima.mm"
include "syl.mm"
include "3syl.mm"
include "syl6reqr.mm"
include "crg.mm"
include "subrgring.mm"
include "mplring.mm"
include "sylan2.mm"
include "3adant2.mm"
include "subrgid.mm"
include "rhmima.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem mpfsubrg
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  assume mpfsubrg.q: |- Q = ran ( ( I evalSub S ) ` R )


  assert |- ( ( I e. V /\ S e. CRing /\ R e. ( SubRing ` S ) ) -> Q e. ( SubRing ` ( S ^s ( ( Base ` S ) ^m I ) ) ) )

  proof
    cI
    cV
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    w3a
    #
    cQ
    cR
    cI
    cS
    ces
    co
    cfv
    #
    cI
    cS
    cR
    cress
    co
    #
    cmpl
    co
    #
    cbs
    cfv
    #
    cima
    #
    cS
    cS
    cbs
    cfv
    #
    cI
    cmap
    co
    cpws
    co
    #
    csubrg
    cfv
    #
    @3
    @8
    @4
    crn
    #
    cQ
    @3
    @4
    @6
    @10
    crh
    co
    wcel
    #
    @7
    @10
    cbs
    cfv
    #
    @4
    wf
    #
    @8
    @12
    wceq
    #
    @9
    @4
    cR
    cS
    @10
    @5
    cI
    cV
    @6
    @4
    eqid
    @6
    eqid
    #
    @5
    eqid
    #
    @10
    eqid
    @9
    eqid
    evlsrhm
    #
    @7
    @14
    @6
    @10
    @4
    @7
    eqid
    #
    @14
    eqid
    rhmf
    @15
    @4
    @7
    wfn
    @16
    @7
    @14
    @4
    ffn
    @7
    @4
    fnima
    syl
    3syl
    mpfsubrg.q
    syl6reqr
    @3
    @13
    @7
    @6
    csubrg
    cfv
    wcel
    #
    @8
    @11
    wcel
    @19
    @3
    @6
    crg
    wcel
    #
    @21
    @0
    @2
    @22
    @1
    @2
    @0
    @5
    crg
    wcel
    @22
    cR
    cS
    @5
    @18
    subrgring
    @6
    @5
    cI
    cV
    @17
    mplring
    sylan2
    3adant2
    @7
    @6
    @20
    subrgid
    syl
    @4
    @6
    @10
    @7
    rhmima
    syl2anc
    eqeltrd
end
