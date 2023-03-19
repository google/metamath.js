include "cplig.mm"
include "wcel.mm"
include "cuni.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cuhgr.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wf1o.mm"
include "wi.mm"
include "f1oi.mm"
include "f1of.mm"
include "wss.mm"
include "pwuni.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wn.mm"
include "n0lplig.mm"
include "adantr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "wb.mm"
include "reldisj.mm"
include "adantl.mm"
include "mpbid.mm"
include "mpan2.mm"
include "fss.mm"
include "sylan2.mm"
include "ex.mm"
include "mp2b.mm"
include "ffdmd.mm"
include "cvv.mm"
include "uniexg.mm"
include "resiexg.mm"
include "isuhgrop.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem pliguhgr
  let cG: class G


  assert |- ( G e. Plig -> <. U. G , ( _I |` G ) >. e. UHGraph )

  proof
    cG
    cplig
    wcel
    #
    cG
    cuni
    #
    cid
    cG
    cres
    #
    cop
    cuhgr
    wcel
    #
    @2
    cdm
    @1
    cpw
    #
    c0
    csn
    #
    cdif
    #
    @2
    wf
    #
    @0
    cG
    @6
    @2
    cG
    cG
    @2
    wf1o
    cG
    cG
    @2
    wf
    #
    @0
    cG
    @6
    @2
    wf
    #
    wi
    cG
    f1oi
    cG
    cG
    @2
    f1of
    @8
    @0
    @9
    @0
    @8
    cG
    @6
    wss
    #
    @9
    @0
    cG
    @4
    wss
    #
    @10
    cG
    pwuni
    @0
    @11
    wa
    #
    cG
    @5
    cin
    c0
    wceq
    #
    @10
    @12
    c0
    cG
    wcel
    wn
    #
    @13
    @0
    @14
    @11
    cG
    n0lplig
    adantr
    cG
    c0
    disjsn
    sylibr
    @11
    @13
    @10
    wb
    @0
    cG
    @5
    @4
    reldisj
    adantl
    mpbid
    mpan2
    cG
    cG
    @6
    @2
    fss
    sylan2
    ex
    mp2b
    ffdmd
    @0
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    @7
    wb
    cG
    cplig
    uniexg
    cG
    cplig
    resiexg
    @2
    @1
    cvv
    cvv
    isuhgrop
    syl2anc
    mpbird
end
