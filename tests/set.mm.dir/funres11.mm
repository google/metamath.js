include "cres.mm"
include "wss.mm"
include "ccnv.mm"
include "wfun.mm"
include "wi.mm"
include "resss.mm"
include "cnvss.mm"
include "funss.mm"
include "mp2b.mm"

theorem funres11
  let cA: class A
  let cF: class F


  assert |- ( Fun `' F -> Fun `' ( F |` A ) )

  proof
    cF
    cA
    cres
    #
    cF
    wss
    @0
    ccnv
    #
    cF
    ccnv
    #
    wss
    @2
    wfun
    @1
    wfun
    wi
    cF
    cA
    resss
    @0
    cF
    cnvss
    @1
    @2
    funss
    mp2b
end
