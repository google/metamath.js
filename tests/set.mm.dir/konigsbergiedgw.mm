include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cs7.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "crab.mm"
include "cword.mm"
include "wcel.mm"
include "wtru.mm"
include "cn0.mm"
include "3nn0.mm"
include "0elfz.mm"
include "ax-mp.mm"
include "cle.mm"
include "wbr.mm"
include "1nn0.mm"
include "1le3.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "0ne1.mm"
include "umgrbi.mm"
include "a1i.mm"
include "2nn0.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "0ne2.mm"
include "nn0fz0.mm"
include "mpbi.mm"
include "3ne0.mm"
include "necomi.mm"
include "1ne2.mm"
include "ltneii.mm"
include "s7cld.mm"
include "trud.mm"
include "pweqi.mm"
include "rabeq.mm"
include "wrdeqi.mm"
include "3eltr4i.mm"

theorem konigsbergiedgw
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.

  disjoint V x
  assert |- E e. Word { x e. ~P V | ( # ` x ) = 2 }

  proof
    cc0
    c1
    cpr
    #
    cc0
    c2
    cpr
    #
    cc0
    c3
    cpr
    #
    c1
    c2
    cpr
    #
    @3
    c2
    c3
    cpr
    #
    @4
    cs7
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cc0
    c3
    cfz
    co
    #
    cpw
    #
    crab
    #
    cword
    #
    cE
    @6
    vx
    cV
    cpw
    #
    crab
    #
    cword
    @5
    @10
    wcel
    wtru
    @0
    @1
    @2
    @3
    @3
    @4
    @4
    @9
    @0
    @9
    wcel
    wtru
    vx
    @7
    cc0
    c1
    c3
    cn0
    wcel
    #
    cc0
    @7
    wcel
    3nn0
    c3
    0elfz
    ax-mp
    #
    c1
    @7
    wcel
    c1
    cn0
    wcel
    @13
    c1
    c3
    cle
    wbr
    1nn0
    3nn0
    1le3
    c1
    c3
    elfz2nn0
    mpbir3an
    #
    0ne1
    umgrbi
    a1i
    @1
    @9
    wcel
    wtru
    vx
    @7
    cc0
    c2
    @14
    c2
    @7
    wcel
    c2
    cn0
    wcel
    @13
    c2
    c3
    cle
    wbr
    2nn0
    3nn0
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    c2
    c3
    elfz2nn0
    mpbir3an
    #
    0ne2
    umgrbi
    a1i
    @2
    @9
    wcel
    wtru
    vx
    @7
    cc0
    c3
    @14
    @13
    c3
    @7
    wcel
    3nn0
    c3
    nn0fz0
    mpbi
    #
    c3
    cc0
    3ne0
    necomi
    umgrbi
    a1i
    @3
    @9
    wcel
    wtru
    vx
    @7
    c1
    c2
    @15
    @16
    1ne2
    umgrbi
    a1i
    #
    @18
    @4
    @9
    wcel
    wtru
    vx
    @7
    c2
    c3
    @16
    @17
    c2
    c3
    2re
    2lt3
    ltneii
    umgrbi
    a1i
    #
    @19
    s7cld
    trud
    konigsberg.e
    @12
    @9
    @11
    @8
    wceq
    @12
    @9
    wceq
    cV
    @7
    konigsberg.v
    pweqi
    @6
    vx
    @11
    @8
    rabeq
    ax-mp
    wrdeqi
    3eltr4i
end
