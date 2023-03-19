include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "ccrd.mm"
include "cfv.mm"
include "ccnv.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "fzennn.mm"
include "carden2b.mm"
include "syl.mm"
include "com.mm"
include "cc0.mm"
include "cuz.mm"
include "wf1o.mm"
include "0z.mm"
include "om2uzf1oi.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "f1ocnvdm.mm"
include "sylancr.mm"
include "cardnn.mm"
include "eqtrd.mm"

theorem cardfz
  let vx: setvar x
  let cG: class G
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  assume fzennn.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )


  assert |- ( N e. NN0 -> ( card ` ( 1 ... N ) ) = ( `' G ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    ccrd
    cfv
    #
    cN
    cG
    ccnv
    cfv
    #
    ccrd
    cfv
    #
    @3
    @0
    @1
    @3
    cen
    wbr
    @2
    @4
    wceq
    vx
    cG
    cN
    fzennn.1
    fzennn
    @1
    @3
    carden2b
    syl
    @0
    @3
    com
    wcel
    #
    @4
    @3
    wceq
    @0
    com
    cc0
    cuz
    cfv
    #
    cG
    wf1o
    cN
    @6
    wcel
    #
    @5
    vx
    cc0
    cG
    0z
    fzennn.1
    om2uzf1oi
    @0
    @7
    cN
    elnn0uz
    biimpi
    com
    @6
    cN
    cG
    f1ocnvdm
    sylancr
    @3
    cardnn
    syl
    eqtrd
end
