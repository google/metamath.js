include "cvv.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "hashprg.mm"
include "biimp3a.mm"
include "wi.mm"
include "wn.mm"
include "elprchashprn2.mm"
include "pm2.21.mm"
include "syl.mm"
include "prcom.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "sylnbi.mm"
include "wa.mm"
include "simpll.mm"
include "simplr.mm"
include "biimpar.mm"
include "3jca.mm"
include "ex.mm"
include "ecase.mm"
include "impbii.mm"

theorem hashprb
  let cM: class M
  let cN: class N


  assert |- ( ( M e. _V /\ N e. _V /\ M =/= N ) <-> ( # ` { M , N } ) = 2 )

  proof
    cM
    cvv
    wcel
    #
    cN
    cvv
    wcel
    #
    cM
    cN
    wne
    #
    w3a
    #
    cM
    cN
    cpr
    #
    chash
    cfv
    #
    c2
    wceq
    #
    @0
    @1
    @2
    @6
    cM
    cN
    cvv
    cvv
    hashprg
    #
    biimp3a
    @0
    @1
    @6
    @3
    wi
    #
    @0
    wn
    @6
    wn
    @8
    cM
    cN
    elprchashprn2
    @6
    @3
    pm2.21
    #
    syl
    @1
    wn
    cN
    cM
    cpr
    #
    chash
    cfv
    #
    c2
    wceq
    #
    wn
    @8
    cN
    cM
    elprchashprn2
    @12
    @6
    @8
    @11
    @5
    c2
    @10
    @4
    chash
    cN
    cM
    prcom
    fveq2i
    eqeq1i
    @9
    sylnbi
    syl
    @0
    @1
    wa
    #
    @6
    @3
    @13
    @6
    wa
    @0
    @1
    @2
    @0
    @1
    @6
    simpll
    @0
    @1
    @6
    simplr
    @13
    @2
    @6
    @7
    biimpar
    3jca
    ex
    ecase
    impbii
end
