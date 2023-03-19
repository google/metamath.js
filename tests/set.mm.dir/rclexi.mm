include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "ssun1.mm"
include "dmun.mm"
include "dmresi.mm"
include "uneq2i.mm"
include "wceq.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "3eqtri.mm"
include "rnun.mm"
include "rnresi.mm"
include "ssun2.mm"
include "uneq12i.mm"
include "unidm.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "eqsstri.mm"
include "wex.mm"
include "elexi.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexd.mm"
include "ax-mp.mm"
include "unex.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "id.mm"
include "sseq12d.mm"
include "cleq2lem.mm"
include "spcev.mm"
include "intexab.mm"
include "sylib.mm"
include "mp2an.mm"

theorem rclexi
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume rclexi.1: |- A e. V

  disjoint A x
  assert |- |^| { x | ( A C_ x /\ ( _I |` ( dom x u. ran x ) ) C_ x ) } e. _V

  proof
    cA
    cA
    cid
    cA
    cdm
    #
    cA
    crn
    #
    cun
    #
    cres
    #
    cun
    #
    wss
    #
    cid
    @4
    cdm
    #
    @4
    crn
    #
    cun
    #
    cres
    #
    @4
    wss
    #
    cA
    vx
    cv
    #
    wss
    cid
    @11
    cdm
    #
    @11
    crn
    #
    cun
    #
    cres
    #
    @11
    wss
    #
    wa
    #
    vx
    cab
    cint
    cvv
    wcel
    #
    cA
    @3
    ssun1
    @9
    @3
    @4
    @8
    @2
    cid
    @8
    @2
    @2
    cun
    @2
    @6
    @2
    @7
    @2
    @6
    @0
    @3
    cdm
    #
    cun
    @0
    @2
    cun
    #
    @2
    cA
    @3
    dmun
    @19
    @2
    @0
    @2
    dmresi
    uneq2i
    @0
    @2
    wss
    @20
    @2
    wceq
    @0
    @1
    ssun1
    @0
    @2
    ssequn1
    mpbi
    3eqtri
    @7
    @1
    @3
    crn
    #
    cun
    @1
    @2
    cun
    #
    @2
    cA
    @3
    rnun
    @21
    @2
    @1
    @2
    rnresi
    uneq2i
    @1
    @2
    wss
    @22
    @2
    wceq
    @1
    @0
    ssun2
    @1
    @2
    ssequn1
    mpbi
    3eqtri
    uneq12i
    @2
    unidm
    eqtri
    reseq2i
    @3
    cA
    ssun2
    eqsstri
    @5
    @10
    wa
    #
    @17
    vx
    wex
    @18
    @17
    @23
    vx
    @4
    cA
    @3
    cA
    cV
    rclexi.1
    elexi
    cA
    cV
    wcel
    #
    @3
    cvv
    wcel
    rclexi.1
    @24
    @2
    cvv
    @24
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    cA
    cV
    dmexg
    cA
    cV
    rnexg
    @0
    @1
    cvv
    cvv
    unexg
    syl2anc
    resiexd
    ax-mp
    unex
    @16
    @10
    @11
    @4
    cA
    @11
    @4
    wceq
    #
    @15
    @9
    @11
    @4
    @25
    @14
    @8
    cid
    @25
    @12
    @6
    @13
    @7
    @11
    @4
    dmeq
    @11
    @4
    rneq
    uneq12d
    reseq2d
    @25
    id
    sseq12d
    cleq2lem
    spcev
    @17
    vx
    intexab
    sylib
    mp2an
end
