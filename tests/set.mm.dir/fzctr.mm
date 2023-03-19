include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "caddc.mm"
include "cr.mm"
include "nn0re.mm"
include "nn0addge1.mm"
include "mpancom.mm"
include "nn0cn.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "cz.mm"
include "wa.mm"
include "wb.mm"
include "nn0z.mm"
include "0zd.mm"
include "2z.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem fzctr
  let cN: class N


  assert |- ( N e. NN0 -> N e. ( 0 ... ( 2 x. N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    c2
    cN
    cmul
    co
    #
    cfz
    co
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    cN
    @1
    cle
    wbr
    #
    cN
    nn0ge0
    @0
    cN
    cN
    cN
    caddc
    co
    #
    @1
    cle
    cN
    cr
    wcel
    @0
    cN
    @5
    cle
    wbr
    cN
    nn0re
    cN
    cN
    nn0addge1
    mpancom
    @0
    cN
    cN
    nn0cn
    2timesd
    breqtrrd
    @0
    cN
    cz
    wcel
    #
    cc0
    cz
    wcel
    @1
    cz
    wcel
    #
    @2
    @3
    @4
    wa
    wb
    cN
    nn0z
    #
    @0
    0zd
    @0
    c2
    cz
    wcel
    @6
    @7
    2z
    @8
    c2
    cN
    zmulcl
    sylancr
    cN
    cc0
    @1
    elfz
    syl3anc
    mpbir2and
end
