include "c0.mm"
include "wf1.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "f0.mm"
include "fun0.mm"
include "cnv0.mm"
include "funeqi.mm"
include "mpbir.mm"
include "df-f1.mm"
include "mpbir2an.mm"

theorem f10
  let cA: class A


  assert |- (/) : (/) -1-1-> A

  proof
    c0
    cA
    c0
    wf1
    c0
    cA
    c0
    wf
    c0
    ccnv
    #
    wfun
    #
    cA
    f0
    @1
    c0
    wfun
    fun0
    @0
    c0
    cnv0
    funeqi
    mpbir
    c0
    cA
    c0
    df-f1
    mpbir2an
end
