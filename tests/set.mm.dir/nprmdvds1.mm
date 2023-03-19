include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "1nprm.mm"
include "wceq.mm"
include "cn0.mm"
include "wb.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "dvds1.mm"
include "syl.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "sylbid.mm"
include "mtoi.mm"

theorem nprmdvds1
  let cP: class P


  assert |- ( P e. Prime -> -. P || 1 )

  proof
    cP
    cprime
    wcel
    #
    cP
    c1
    cdvds
    wbr
    #
    c1
    cprime
    wcel
    #
    1nprm
    @0
    @1
    cP
    c1
    wceq
    #
    @2
    @0
    cP
    cn0
    wcel
    @1
    @3
    wb
    @0
    cP
    cP
    prmnn
    nnnn0d
    cP
    dvds1
    syl
    @3
    @0
    @2
    cP
    c1
    cprime
    eleq1
    biimpcd
    sylbid
    mtoi
end
