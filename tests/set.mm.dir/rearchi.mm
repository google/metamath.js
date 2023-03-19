include "crefld.mm"
include "carchi.mm"
include "wcel.mm"
include "cv.mm"
include "czrh.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "cr.mm"
include "cofld.mm"
include "wral.mm"
include "wb.mm"
include "reofld.mm"
include "rebase.mm"
include "eqid.mm"
include "relt.mm"
include "isarchiofld.mm"
include "ax-mp.mm"
include "arch.mm"
include "cz.mm"
include "nnz.mm"
include "c1.mm"
include "cmg.mm"
include "co.mm"
include "cmul.mm"
include "crg.mm"
include "wceq.mm"
include "cfield.mm"
include "cdr.mm"
include "refld.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "drngring.mm"
include "mp2b.mm"
include "re1r.mm"
include "zrhmulg.mm"
include "mpan.mm"
include "1re.mm"
include "remulg.mm"
include "mpan2.mm"
include "zcn.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "breq2d.mm"
include "syl.mm"
include "rexbiia.mm"
include "sylibr.mm"
include "mprgbir.mm"

theorem rearchi
  let vn: setvar n
  let vx: setvar x


  assert |- RRfld e. Archi

  proof
    crefld
    carchi
    wcel
    #
    vx
    cv
    #
    vn
    cv
    #
    crefld
    czrh
    cfv
    #
    cfv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    vx
    cr
    crefld
    cofld
    wcel
    @0
    @6
    vx
    cr
    wral
    wb
    reofld
    vx
    cr
    clt
    vn
    @3
    crefld
    rebase
    @3
    eqid
    #
    relt
    isarchiofld
    ax-mp
    @1
    cr
    wcel
    @1
    @2
    clt
    wbr
    #
    vn
    cn
    wrex
    @6
    @1
    vn
    arch
    @5
    @8
    vn
    cn
    @2
    cn
    wcel
    @2
    cz
    wcel
    #
    @5
    @8
    wb
    @2
    nnz
    @9
    @4
    @2
    @1
    clt
    @9
    @4
    @2
    c1
    crefld
    cmg
    cfv
    #
    co
    #
    @2
    c1
    cmul
    co
    #
    @2
    crefld
    crg
    wcel
    #
    @9
    @4
    @11
    wceq
    crefld
    cfield
    wcel
    #
    crefld
    cdr
    wcel
    #
    @13
    refld
    @14
    @15
    crefld
    ccrg
    wcel
    crefld
    isfld
    simplbi
    crefld
    drngring
    mp2b
    crefld
    @10
    c1
    @3
    @2
    @7
    @10
    eqid
    re1r
    zrhmulg
    mpan
    @9
    c1
    cr
    wcel
    @11
    @12
    wceq
    1re
    c1
    @2
    remulg
    mpan2
    @9
    @2
    @2
    zcn
    mulid1d
    3eqtrd
    breq2d
    syl
    rexbiia
    sylibr
    mprgbir
end
