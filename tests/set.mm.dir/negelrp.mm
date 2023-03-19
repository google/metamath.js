include "cneg.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "elrp.mm"
include "lt0neg1.mm"
include "renegcl.mm"
include "biantrurd.mm"
include "bitr2d.mm"
include "syl5bb.mm"

theorem negelrp
  let cA: class A


  assert |- ( A e. RR -> ( -u A e. RR+ <-> A < 0 ) )

  proof
    cA
    cneg
    #
    crp
    wcel
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wa
    #
    cA
    cr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    @0
    elrp
    @4
    @5
    @2
    @3
    cA
    lt0neg1
    @4
    @1
    @2
    cA
    renegcl
    biantrurd
    bitr2d
    syl5bb
end
