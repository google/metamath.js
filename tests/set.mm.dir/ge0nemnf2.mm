include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cmnf.mm"
include "wne.mm"
include "eliccxr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "id.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"

theorem ge0nemnf2
  let cA: class A


  assert |- ( A e. ( 0 [,] +oo ) -> A =/= -oo )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    wcel
    #
    cA
    cxr
    wcel
    cc0
    cA
    cle
    wbr
    #
    cA
    cmnf
    wne
    cA
    cc0
    cpnf
    eliccxr
    @0
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @0
    @1
    @2
    @0
    0xr
    a1i
    @3
    @0
    pnfxr
    a1i
    @0
    id
    cc0
    cpnf
    cA
    iccgelb
    syl3anc
    cA
    ge0nemnf
    syl2anc
end
