include "cid.mm"
include "ccnv.mm"
include "wceq.mm"
include "wfun.mm"
include "cres.mm"
include "cnvi.mm"
include "eqcomi.mm"
include "funi.mm"
include "funeq.mm"
include "mpbii.mm"
include "cima.mm"
include "funcnvres.mm"
include "imai.mm"
include "reseq12i.mm"
include "syl6eq.mm"
include "mp2b.mm"

theorem cnvresid
  let cA: class A


  assert |- `' ( _I |` A ) = ( _I |` A )

  proof
    cid
    cid
    ccnv
    #
    wceq
    #
    @0
    wfun
    #
    cid
    cA
    cres
    #
    ccnv
    #
    @3
    wceq
    @0
    cid
    cnvi
    eqcomi
    @1
    cid
    wfun
    @2
    funi
    cid
    @0
    funeq
    mpbii
    @2
    @4
    @0
    cid
    cA
    cima
    #
    cres
    @3
    cA
    cid
    funcnvres
    @0
    cid
    @5
    cA
    cnvi
    cA
    imai
    reseq12i
    syl6eq
    mp2b
end
