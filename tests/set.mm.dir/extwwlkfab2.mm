include "wcel.mm"
include "c2.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "cclwwlknon.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "cmin.mm"
include "wa.mm"
include "eqeq2.mm"
include "anbi1d.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "2cn.mm"
include "subidi.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "biantrud.mm"
include "bicomd.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "mpan2.mm"
include "clwwlknon.mm"
include "syl6eqr.mm"

theorem extwwlkfab2
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cG: class G
  let cV: class V
  let cX: class X
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  assert |- ( X e. V -> ( X C 2 ) = ( X ( ClWWalksNOn ` G ) 2 ) )

  proof
    cX
    cV
    wcel
    #
    cX
    c2
    cC
    co
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    vw
    c2
    cG
    cclwwlkn
    co
    #
    crab
    #
    cX
    c2
    cG
    cclwwlknon
    cfv
    co
    @0
    c2
    c2
    cuz
    cfv
    #
    wcel
    #
    @1
    @6
    wceq
    c2
    cz
    wcel
    @8
    2z
    c2
    uzid
    ax-mp
    vv
    vn
    cX
    c2
    cV
    @7
    @3
    vv
    cv
    #
    wceq
    #
    vn
    cv
    #
    c2
    cmin
    co
    #
    @2
    cfv
    @3
    wceq
    #
    wa
    #
    vw
    @11
    cG
    cclwwlkn
    co
    #
    crab
    @6
    cC
    @4
    @13
    wa
    #
    vw
    @15
    crab
    @9
    cX
    wceq
    #
    @14
    @16
    vw
    @15
    @17
    @10
    @4
    @13
    @9
    cX
    @3
    eqeq2
    anbi1d
    rabbidv
    @11
    c2
    wceq
    #
    @16
    @4
    vw
    @15
    @5
    @11
    c2
    cG
    cclwwlkn
    oveq1
    @18
    @4
    @16
    @18
    @13
    @4
    @18
    @12
    cc0
    @2
    @18
    @12
    c2
    c2
    cmin
    co
    cc0
    @11
    c2
    c2
    cmin
    oveq1
    c2
    2cn
    subidi
    syl6eq
    fveq2d
    biantrud
    bicomd
    rabeqbidv
    extwwlkfab.c
    @4
    vw
    @5
    c2
    cG
    cclwwlkn
    ovex
    rabex
    ovmpt2
    mpan2
    vw
    cG
    c2
    cX
    clwwlknon
    syl6eqr
end
