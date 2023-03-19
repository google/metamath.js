include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "ccnv.mm"
include "wfun.mm"
include "c1.mm"
include "cs2.mm"
include "cvv.mm"
include "simp1.mm"
include "anim2i.mm"
include "ancomd.mm"
include "3simpc.mm"
include "adantl.mm"
include "usgr2wlkneq.mm"
include "syl2anc.mm"
include "fvexd.mm"
include "simpr.mm"
include "3jca.mm"
include "funcnvs2.mm"
include "3syl.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "eqid.mm"
include "wlkf.mm"
include "simp2.mm"
include "wrdlen2s2.mm"
include "syl2an.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem usgr2wlkspthlem1
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( Walks ` G ) P /\ ( G e. USGraph /\ ( # ` F ) = 2 /\ ( P ` 0 ) =/= ( P ` ( # ` F ) ) ) ) -> Fun `' F )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cG
    cusgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    cc0
    cP
    cfv
    #
    @2
    cP
    cfv
    wne
    #
    w3a
    #
    wa
    #
    cF
    ccnv
    #
    wfun
    cc0
    cF
    cfv
    #
    c1
    cF
    cfv
    #
    cs2
    #
    ccnv
    #
    wfun
    #
    @7
    @4
    c1
    cP
    cfv
    #
    wne
    @4
    c2
    cP
    cfv
    #
    wne
    @14
    @15
    wne
    w3a
    #
    @9
    @10
    wne
    #
    wa
    #
    @9
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    @17
    w3a
    @13
    @7
    @1
    @0
    wa
    @3
    @5
    wa
    #
    @18
    @7
    @0
    @1
    @6
    @1
    @0
    @1
    @3
    @5
    simp1
    anim2i
    ancomd
    @6
    @21
    @0
    @1
    @3
    @5
    3simpc
    adantl
    cP
    cF
    cG
    usgr2wlkneq
    syl2anc
    @18
    @19
    @20
    @17
    @18
    cc0
    cF
    fvexd
    @18
    c1
    cF
    fvexd
    @16
    @17
    simpr
    3jca
    @9
    @10
    cvv
    funcnvs2
    3syl
    @7
    @8
    @12
    @7
    cF
    @11
    @0
    cF
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    @3
    cF
    @11
    wceq
    @6
    cP
    cF
    cG
    @22
    @22
    eqid
    wlkf
    @1
    @3
    @5
    simp2
    @23
    cF
    wrdlen2s2
    syl2an
    cnveqd
    funeqd
    mpbird
end
