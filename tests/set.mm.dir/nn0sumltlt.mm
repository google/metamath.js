include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "ltaddsub2.mm"
include "syl3an.mm"
include "cle.mm"
include "cc0.mm"
include "nn0ge0.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "anim12ci.mm"
include "3adant2.mm"
include "subge02.mm"
include "bicomd.mm"
include "syl.mm"
include "mpbird.mm"
include "wi.mm"
include "3ad2ant2.mm"
include "nn0resubcl.mm"
include "ancoms.mm"
include "3ad2ant3.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbid.mm"

theorem nn0sumltlt
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( a e. NN0 /\ b e. NN0 /\ c e. NN0 ) -> ( ( a + b ) < c -> b < c ) )

  proof
    va
    cv
    #
    cn0
    wcel
    #
    vb
    cv
    #
    cn0
    wcel
    #
    vc
    cv
    #
    cn0
    wcel
    #
    w3a
    #
    @0
    @2
    caddc
    co
    @4
    clt
    wbr
    #
    @2
    @4
    @0
    cmin
    co
    #
    clt
    wbr
    #
    @2
    @4
    clt
    wbr
    #
    @1
    @0
    cr
    wcel
    #
    @3
    @2
    cr
    wcel
    #
    @5
    @4
    cr
    wcel
    #
    @7
    @9
    wb
    @0
    nn0re
    #
    @2
    nn0re
    #
    @4
    nn0re
    #
    @0
    @2
    @4
    ltaddsub2
    syl3an
    @6
    @9
    @8
    @4
    cle
    wbr
    #
    @10
    @6
    @17
    cc0
    @0
    cle
    wbr
    #
    @1
    @3
    @18
    @5
    @0
    nn0ge0
    3ad2ant1
    @6
    @13
    @11
    wa
    #
    @17
    @18
    wb
    @1
    @5
    @19
    @3
    @1
    @11
    @5
    @13
    @14
    @16
    anim12ci
    3adant2
    @19
    @18
    @17
    @4
    @0
    subge02
    bicomd
    syl
    mpbird
    @6
    @12
    @8
    cr
    wcel
    #
    @13
    @9
    @17
    wa
    @10
    wi
    @3
    @1
    @12
    @5
    @15
    3ad2ant2
    @1
    @5
    @20
    @3
    @5
    @1
    @20
    @4
    @0
    nn0resubcl
    ancoms
    3adant2
    @5
    @1
    @13
    @3
    @16
    3ad2ant3
    @2
    @8
    @4
    ltletr
    syl3anc
    mpan2d
    sylbid
end
