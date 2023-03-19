include "c1.mm"
include "cprime.mm"
include "wcel.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "c2o.mm"
include "cen.mm"
include "csdm.mm"
include "wn.mm"
include "c1o.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "1nn.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0.mm"
include "dvds1.mm"
include "syl.mm"
include "bicomd.mm"
include "biadan2.mm"
include "velsn.mm"
include "breq1.mm"
include "elrab.mm"
include "3bitr4ri.mm"
include "eqriv.mm"
include "1ex.mm"
include "ensn1.mm"
include "eqbrtri.mm"
include "1sdom2.mm"
include "ensdomtr.mm"
include "mp2an.mm"
include "sdomnen.mm"
include "ax-mp.mm"
include "isprm.mm"
include "mpbiran.mm"
include "mtbir.mm"

theorem 1nprm
  let vn: setvar n
  let vz: setvar z


  assert |- -. 1 e. Prime

  proof
    c1
    cprime
    wcel
    #
    vn
    cv
    #
    c1
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    c2o
    cen
    wbr
    #
    @3
    c2o
    csdm
    wbr
    #
    @4
    wn
    @3
    c1o
    cen
    wbr
    c1o
    c2o
    csdm
    wbr
    @5
    @3
    c1
    csn
    #
    c1o
    cen
    vz
    @3
    @6
    vz
    cv
    #
    c1
    wceq
    #
    @7
    cn
    wcel
    #
    @7
    c1
    cdvds
    wbr
    #
    wa
    @7
    @6
    wcel
    @7
    @3
    wcel
    @8
    @9
    @10
    @8
    @9
    c1
    cn
    wcel
    #
    1nn
    @7
    c1
    cn
    eleq1
    mpbiri
    @9
    @10
    @8
    @9
    @7
    cn0
    wcel
    @10
    @8
    wb
    @7
    nnnn0
    @7
    dvds1
    syl
    bicomd
    biadan2
    vz
    c1
    velsn
    @2
    @10
    vn
    @7
    cn
    @1
    @7
    c1
    cdvds
    breq1
    elrab
    3bitr4ri
    eqriv
    c1
    1ex
    ensn1
    eqbrtri
    1sdom2
    @3
    c1o
    c2o
    ensdomtr
    mp2an
    @3
    c2o
    sdomnen
    ax-mp
    @0
    @11
    @4
    1nn
    c1
    vn
    isprm
    mpbiran
    mtbir
end
