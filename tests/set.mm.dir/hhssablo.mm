include "csh.mm"
include "wcel.mm"
include "cva.mm"
include "cxp.mm"
include "cres.mm"
include "cablo.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "eqtrd.mm"
include "reseq2d.mm"
include "eleq1d.mm"
include "helsh.mm"
include "elimel.mm"
include "hhssabloi.mm"
include "dedth.mm"

theorem hhssablo
  let cH: class H


  assert |- ( H e. SH -> ( +h |` ( H X. H ) ) e. AbelOp )

  proof
    cH
    csh
    wcel
    #
    cva
    cH
    cH
    cxp
    #
    cres
    #
    cablo
    wcel
    cva
    @0
    cH
    chil
    cif
    #
    @3
    cxp
    #
    cres
    #
    cablo
    wcel
    cH
    chil
    cH
    @3
    wceq
    #
    @2
    @5
    cablo
    @6
    @1
    @4
    cva
    @6
    @1
    @3
    cH
    cxp
    @4
    cH
    @3
    cH
    xpeq1
    cH
    @3
    @3
    xpeq2
    eqtrd
    reseq2d
    eleq1d
    @3
    cH
    chil
    csh
    helsh
    elimel
    hhssabloi
    dedth
end
