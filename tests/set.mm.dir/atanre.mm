include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "wne.mm"
include "catan.mm"
include "cdm.mm"
include "recn.mm"
include "neg1rr.mm"
include "a1i.mm"
include "cc0.mm"
include "0red.mm"
include "resqcl.mm"
include "clt.mm"
include "wbr.mm"
include "neg1lt0.mm"
include "sqge0.mm"
include "ltletrd.mm"
include "gtned.mm"
include "atandm3.mm"
include "sylanbrc.mm"

theorem atanre
  let cA: class A


  assert |- ( A e. RR -> A e. dom arctan )

  proof
    cA
    cr
    wcel
    #
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    cA
    catan
    cdm
    wcel
    cA
    recn
    @0
    @2
    @1
    @2
    cr
    wcel
    @0
    neg1rr
    a1i
    #
    @0
    @2
    cc0
    @1
    @3
    @0
    0red
    cA
    resqcl
    @2
    cc0
    clt
    wbr
    @0
    neg1lt0
    a1i
    cA
    sqge0
    ltletrd
    gtned
    cA
    atandm3
    sylanbrc
end
