include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "wceq.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "wo.mm"
include "iccssxr.mm"
include "sseli.mm"
include "xrge0neqmnf.mm"
include "wa.mm"
include "xrnemnf.mm"
include "biimpi.mm"
include "syl2anc.mm"
include "orcanai.mm"

theorem xrge0nre
  let cA: class A


  assert |- ( ( A e. ( 0 [,] +oo ) /\ -. A e. RR ) -> A = +oo )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    @1
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    @2
    @3
    wo
    #
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    sseli
    cA
    xrge0neqmnf
    @4
    @5
    wa
    @6
    cA
    xrnemnf
    biimpi
    syl2anc
    orcanai
end
