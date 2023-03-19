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
include "cs3.mm"
include "cvv.mm"
include "simp1.mm"
include "anim2i.mm"
include "ancomd.mm"
include "3simpc.mm"
include "adantl.mm"
include "usgr2wlkneq.mm"
include "syl2anc.mm"
include "simpl.mm"
include "fvex.mm"
include "3pm3.2i.mm"
include "jctil.mm"
include "funcnvs3.mm"
include "3syl.mm"
include "cvtx.mm"
include "cword.mm"
include "c3.mm"
include "eqid.mm"
include "wlkpwrd.mm"
include "caddc.mm"
include "co.mm"
include "wlklenvp1.mm"
include "oveq1.mm"
include "2p1e3.mm"
include "syl6eq.mm"
include "3ad2ant2.mm"
include "sylan9eq.mm"
include "wrdlen3s3.mm"
include "syl2an2r.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem usgr2wlkspthlem2
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( Walks ` G ) P /\ ( G e. USGraph /\ ( # ` F ) = 2 /\ ( P ` 0 ) =/= ( P ` ( # ` F ) ) ) ) -> Fun `' P )

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
    cP
    ccnv
    #
    wfun
    @4
    c1
    cP
    cfv
    #
    c2
    cP
    cfv
    #
    cs3
    #
    ccnv
    #
    wfun
    #
    @7
    @4
    @9
    wne
    @4
    @10
    wne
    @9
    @10
    wne
    w3a
    #
    cc0
    cF
    cfv
    c1
    cF
    cfv
    wne
    #
    wa
    #
    @4
    cvv
    wcel
    #
    @9
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    w3a
    #
    @14
    wa
    @13
    @7
    @1
    @0
    wa
    @3
    @5
    wa
    #
    @16
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
    @16
    @14
    @20
    @14
    @15
    simpl
    @17
    @18
    @19
    cc0
    cP
    fvex
    c1
    cP
    fvex
    c2
    cP
    fvex
    3pm3.2i
    jctil
    @4
    @9
    @10
    cvv
    funcnvs3
    3syl
    @7
    @8
    @12
    @7
    cP
    @11
    @0
    cP
    cG
    cvtx
    cfv
    #
    cword
    wcel
    @6
    cP
    chash
    cfv
    #
    c3
    wceq
    cP
    @11
    wceq
    cP
    cF
    cG
    @22
    @22
    eqid
    wlkpwrd
    @0
    @6
    @23
    @2
    c1
    caddc
    co
    #
    c3
    cP
    cF
    cG
    wlklenvp1
    @3
    @1
    @24
    c3
    wceq
    @5
    @3
    @24
    c2
    c1
    caddc
    co
    c3
    @2
    c2
    c1
    caddc
    oveq1
    2p1e3
    syl6eq
    3ad2ant2
    sylan9eq
    @22
    cP
    wrdlen3s3
    syl2an2r
    cnveqd
    funeqd
    mpbird
end
