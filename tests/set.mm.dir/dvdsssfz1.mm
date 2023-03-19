include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "cle.mm"
include "cz.mm"
include "nnz.mm"
include "id.mm"
include "dvdsle.mm"
include "syl2anr.mm"
include "wb.mm"
include "ibar.mm"
include "adantl.mm"
include "adantr.mm"
include "fznn.mm"
include "syl.mm"
include "bitr4d.mm"
include "sylibd.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"

theorem dvdsssfz1
  let cA: class A
  let vp: setvar p

  disjoint A p
  assert |- ( A e. NN -> { p e. NN | p || A } C_ ( 1 ... A ) )

  proof
    cA
    cn
    wcel
    #
    vp
    cv
    #
    cA
    cdvds
    wbr
    #
    @1
    c1
    cA
    cfz
    co
    #
    wcel
    #
    wi
    #
    vp
    cn
    wral
    @2
    vp
    cn
    crab
    @3
    wss
    @0
    @5
    vp
    cn
    @0
    @1
    cn
    wcel
    #
    wa
    #
    @2
    @1
    cA
    cle
    wbr
    #
    @4
    @6
    @1
    cz
    wcel
    @0
    @2
    @8
    wi
    @0
    @1
    nnz
    @0
    id
    @1
    cA
    dvdsle
    syl2anr
    @7
    @8
    @6
    @8
    wa
    #
    @4
    @6
    @8
    @9
    wb
    @0
    @6
    @8
    ibar
    adantl
    @7
    cA
    cz
    wcel
    #
    @4
    @9
    wb
    @0
    @10
    @6
    cA
    nnz
    adantr
    @1
    cA
    fznn
    syl
    bitr4d
    sylibd
    ralrimiva
    @2
    vp
    cn
    @3
    rabss
    sylibr
end
