include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "nndiv.mm"
include "cc.mm"
include "nncn.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "rexbidva.mm"
include "wb.mm"
include "nndivdvds.mm"
include "ancoms.mm"
include "3bitr4rd.mm"

theorem nndivides
  let vn: setvar n
  let cM: class M
  let cN: class N

  disjoint M n
  disjoint N n
  assert |- ( ( M e. NN /\ N e. NN ) -> ( M || N <-> E. n e. NN ( n x. M ) = N ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    vn
    cv
    #
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cn
    wrex
    cN
    cM
    cdiv
    co
    cn
    wcel
    #
    @3
    cM
    cmul
    co
    #
    cN
    wceq
    #
    vn
    cn
    wrex
    cM
    cN
    cdvds
    wbr
    #
    vn
    cM
    cN
    nndiv
    @2
    @8
    @5
    vn
    cn
    @2
    @3
    cn
    wcel
    #
    wa
    #
    @7
    @4
    cN
    @11
    @3
    cM
    @10
    @3
    cc
    wcel
    @2
    @3
    nncn
    adantl
    @0
    cM
    cc
    wcel
    @1
    @10
    cM
    nncn
    ad2antrr
    mulcomd
    eqeq1d
    rexbidva
    @1
    @0
    @9
    @6
    wb
    cN
    cM
    nndivdvds
    ancoms
    3bitr4rd
end
