include "c1.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "breq2.mm"
include "1le1.mm"
include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "wi.mm"
include "nnre.mm"
include "cc0.mm"
include "recn.mm"
include "addid1d.mm"
include "breq2d.mm"
include "clt.mm"
include "wn.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "axltadd.mm"
include "mp3an12.mm"
include "mpi.mm"
include "wa.mm"
include "readdcl.mm"
include "mpan2.mm"
include "peano2re.mm"
include "lttr.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mpand.mm"
include "con3d.mm"
include "wb.mm"
include "lenlt.mm"
include "sylancr.mm"
include "3imtr4d.mm"
include "sylbird.mm"
include "syl.mm"
include "nnind.mm"

theorem nnge1
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. NN -> 1 <_ A )

  proof
    c1
    vx
    cv
    #
    cle
    wbr
    c1
    c1
    cle
    wbr
    c1
    vy
    cv
    #
    cle
    wbr
    #
    c1
    @1
    c1
    caddc
    co
    #
    cle
    wbr
    #
    c1
    cA
    cle
    wbr
    vx
    vy
    cA
    @0
    c1
    c1
    cle
    breq2
    @0
    @1
    c1
    cle
    breq2
    @0
    @3
    c1
    cle
    breq2
    @0
    cA
    c1
    cle
    breq2
    1le1
    @1
    cn
    wcel
    @1
    cr
    wcel
    #
    @2
    @4
    wi
    @1
    nnre
    @5
    @2
    c1
    @1
    cc0
    caddc
    co
    #
    cle
    wbr
    #
    @4
    @5
    @6
    @1
    c1
    cle
    @5
    @1
    @1
    recn
    addid1d
    breq2d
    @5
    @6
    c1
    clt
    wbr
    #
    wn
    #
    @3
    c1
    clt
    wbr
    #
    wn
    #
    @7
    @4
    @5
    @10
    @8
    @5
    @6
    @3
    clt
    wbr
    #
    @10
    @8
    @5
    cc0
    c1
    clt
    wbr
    #
    @12
    0lt1
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @5
    @13
    @12
    wi
    0re
    1re
    cc0
    c1
    @1
    axltadd
    mp3an12
    mpi
    @5
    @6
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @12
    @10
    wa
    @8
    wi
    #
    @5
    @14
    @16
    0re
    @1
    cc0
    readdcl
    mpan2
    #
    @1
    peano2re
    #
    @16
    @17
    @15
    @18
    1re
    @6
    @3
    c1
    lttr
    mp3an3
    syl2anc
    mpand
    con3d
    @5
    @15
    @16
    @7
    @9
    wb
    1re
    @19
    c1
    @6
    lenlt
    sylancr
    @5
    @15
    @17
    @4
    @11
    wb
    1re
    @20
    c1
    @3
    lenlt
    sylancr
    3imtr4d
    sylbird
    syl
    nnind
end
