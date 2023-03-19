include "cop.mm"
include "csn.mm"
include "cgr.mm"
include "wcel.mm"
include "cgi.mm"
include "cfv.mm"
include "wceq.mm"
include "grposnOLD.mm"
include "crn.mm"
include "opex.mm"
include "rnsnop.mm"
include "eqcomi.mm"
include "eqid.mm"
include "grpoidcl.mm"
include "elsni.mm"
include "mp2b.mm"

theorem gidsn
  let cA: class A
  assume ablsn.1: |- A e. _V


  assert |- ( GId ` { <. <. A , A >. , A >. } ) = A

  proof
    cA
    cA
    cop
    #
    cA
    cop
    csn
    #
    cgr
    wcel
    @1
    cgi
    cfv
    #
    cA
    csn
    #
    wcel
    @2
    cA
    wceq
    cA
    ablsn.1
    grposnOLD
    @2
    @1
    @3
    @1
    crn
    @3
    @0
    cA
    cA
    cA
    opex
    rnsnop
    eqcomi
    @2
    eqid
    grpoidcl
    @2
    cA
    elsni
    mp2b
end
