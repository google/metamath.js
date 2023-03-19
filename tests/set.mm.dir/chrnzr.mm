include "crg.mm"
include "wcel.mm"
include "cnzr.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cchr.mm"
include "c1.mm"
include "eqid.mm"
include "isnzr.mm"
include "baib.mm"
include "cdvds.mm"
include "wbr.mm"
include "czrh.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "1z.mm"
include "chrdvds.mm"
include "mpan2.mm"
include "cn0.mm"
include "chrcl.mm"
include "dvds1.mm"
include "syl.mm"
include "zrh1.mm"
include "eqeq1d.mm"
include "3bitr3d.mm"
include "necon3bid.mm"
include "bitr4d.mm"

theorem chrnzr
  let cR: class R


  assert |- ( R e. Ring -> ( R e. NzRing <-> ( chr ` R ) =/= 1 ) )

  proof
    cR
    crg
    wcel
    #
    cR
    cnzr
    wcel
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    #
    cR
    cchr
    cfv
    #
    c1
    wne
    @1
    @0
    @4
    cR
    @2
    @3
    @2
    eqid
    #
    @3
    eqid
    #
    isnzr
    baib
    @0
    @5
    c1
    @2
    @3
    @0
    @5
    c1
    cdvds
    wbr
    #
    c1
    cR
    czrh
    cfv
    #
    cfv
    #
    @3
    wceq
    #
    @5
    c1
    wceq
    #
    @2
    @3
    wceq
    @0
    c1
    cz
    wcel
    @8
    @11
    wb
    1z
    @5
    cR
    @9
    c1
    @3
    @5
    eqid
    #
    @9
    eqid
    #
    @7
    chrdvds
    mpan2
    @0
    @5
    cn0
    wcel
    @8
    @12
    wb
    @5
    cR
    @13
    chrcl
    @5
    dvds1
    syl
    @0
    @10
    @2
    @3
    cR
    @2
    @9
    @14
    @6
    zrh1
    eqeq1d
    3bitr3d
    necon3bid
    bitr4d
end
