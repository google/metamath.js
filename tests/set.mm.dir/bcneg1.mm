include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cbc.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cif.mm"
include "cz.mm"
include "wceq.mm"
include "neg1z.mm"
include "bcval.mm"
include "mpan2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wn.mm"
include "neg1lt0.mm"
include "neg1rr.mm"
include "0re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "intnanr.mm"
include "wb.mm"
include "nn0z.mm"
include "0z.mm"
include "elfz.mm"
include "mp3an12.mm"
include "syl.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem bcneg1
  let cN: class N


  assert |- ( N e. NN0 -> ( N _C -u 1 ) = 0 )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    cneg
    #
    cbc
    co
    #
    @1
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cfa
    cfv
    cN
    @1
    cmin
    co
    cfa
    cfv
    @1
    cfa
    cfv
    cmul
    co
    cdiv
    co
    #
    cc0
    cif
    #
    cc0
    @0
    @1
    cz
    wcel
    #
    @2
    @5
    wceq
    neg1z
    @1
    cN
    bcval
    mpan2
    @0
    @3
    @4
    cc0
    @0
    @3
    cc0
    @1
    cle
    wbr
    #
    @1
    cN
    cle
    wbr
    #
    wa
    #
    @7
    @8
    @1
    cc0
    clt
    wbr
    @7
    wn
    neg1lt0
    @1
    cc0
    neg1rr
    0re
    ltnlei
    mpbi
    intnanr
    @0
    cN
    cz
    wcel
    #
    @3
    @9
    wb
    #
    cN
    nn0z
    @6
    cc0
    cz
    wcel
    @10
    @11
    neg1z
    0z
    @1
    cc0
    cN
    elfz
    mp3an12
    syl
    mtbiri
    iffalsed
    eqtrd
end
