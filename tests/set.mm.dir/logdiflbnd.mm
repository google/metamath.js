include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "ce.mm"
include "cfv.mm"
include "clog.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "rpre.mm"
include "rpge0.mm"
include "ge0p1rpd.mm"
include "rprecred.mm"
include "1red.mm"
include "cc0.mm"
include "0le1.mm"
include "a1i.mm"
include "divge0d.mm"
include "clt.mm"
include "cmul.mm"
include "id.mm"
include "ltaddrp2d.mm"
include "readdcld.mm"
include "recnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "ltdivmuld.mm"
include "mpbird.mm"
include "eflegeo.mm"
include "rpne0d.mm"
include "divsubdird.mm"
include "pncand.mm"
include "oveq1d.mm"
include "dividd.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "rpne0.mm"
include "recdivd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "rpefcld.mm"
include "rpdivcld.mm"
include "logled.mm"
include "mpbid.mm"
include "relogefd.mm"
include "relogdivd.mm"
include "3brtr3d.mm"

theorem logdiflbnd
  let cA: class A


  assert |- ( A e. RR+ -> ( 1 / ( A + 1 ) ) <_ ( ( log ` ( A + 1 ) ) - ( log ` A ) ) )

  proof
    cA
    crp
    wcel
    #
    c1
    cA
    c1
    caddc
    co
    #
    cdiv
    co
    #
    ce
    cfv
    #
    clog
    cfv
    #
    @1
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    @2
    @1
    clog
    cfv
    cA
    clog
    cfv
    cmin
    co
    cle
    @0
    @3
    @5
    cle
    wbr
    @4
    @6
    cle
    wbr
    @0
    @3
    c1
    c1
    @2
    cmin
    co
    #
    cdiv
    co
    #
    @5
    cle
    @0
    @2
    @0
    @1
    @0
    cA
    cA
    rpre
    #
    cA
    rpge0
    ge0p1rpd
    #
    rprecred
    #
    @0
    c1
    @1
    @0
    1red
    #
    @10
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    divge0d
    @0
    @2
    c1
    clt
    wbr
    c1
    @1
    c1
    cmul
    co
    #
    clt
    wbr
    @0
    c1
    @1
    @13
    clt
    @0
    c1
    cA
    @12
    @0
    id
    #
    ltaddrp2d
    @0
    @1
    @0
    @1
    @0
    cA
    c1
    @9
    @12
    readdcld
    recnd
    #
    mulid1d
    breqtrrd
    @0
    c1
    c1
    @1
    @12
    @12
    @10
    ltdivmuld
    mpbird
    eflegeo
    @0
    @8
    c1
    cA
    @1
    cdiv
    co
    #
    cdiv
    co
    @5
    @0
    @7
    @16
    c1
    cdiv
    @0
    @1
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    @1
    @1
    cdiv
    co
    #
    @2
    cmin
    co
    @16
    @7
    @0
    @1
    c1
    @1
    @15
    @0
    c1
    @12
    recnd
    #
    @15
    @0
    @1
    @10
    rpne0d
    #
    divsubdird
    @0
    @17
    cA
    @1
    cdiv
    @0
    cA
    c1
    @0
    cA
    @9
    recnd
    #
    @19
    pncand
    oveq1d
    @0
    @18
    c1
    @2
    cmin
    @0
    @1
    @15
    @20
    dividd
    oveq1d
    3eqtr3rd
    oveq2d
    @0
    cA
    @1
    @21
    @15
    cA
    rpne0
    @20
    recdivd
    eqtrd
    breqtrd
    @0
    @3
    @5
    @0
    @2
    @11
    rpefcld
    @0
    @1
    cA
    @10
    @14
    rpdivcld
    logled
    mpbid
    @0
    @2
    @11
    relogefd
    @0
    @1
    cA
    @10
    @14
    relogdivd
    3brtr3d
end
