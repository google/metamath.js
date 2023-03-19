include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "chash.mm"
include "cc0.mm"
include "cpr.mm"
include "wcel.mm"
include "ceupth.mm"
include "c0.mm"
include "wceq.mm"
include "clt.mm"
include "konigsberglem5.mm"
include "wo.mm"
include "elpri.mm"
include "2pos.mm"
include "0re.mm"
include "2re.mm"
include "ltnsymi.mm"
include "ax-mp.mm"
include "breq2.mm"
include "mtbiri.mm"
include "ltnri.mm"
include "jaoi.mm"
include "syl.mm"
include "mt2.mm"
include "cupgr.mm"
include "wne.mm"
include "cumgr.mm"
include "konigsbergumgr.mm"
include "umgrupgr.mm"
include "cvtx.mm"
include "cop.mm"
include "fveq2i.mm"
include "cvv.mm"
include "cword.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "c1.mm"
include "cs7.mm"
include "s7cli.mm"
include "opvtxfv.mm"
include "mp2an.mm"
include "eqtr2i.mm"
include "eulerpath.mm"
include "mpan.mm"
include "necon1bi.mm"

theorem konigsberg
  let cE: class E
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.


  assert |- ( EulerPaths ` G ) = (/)

  proof
    c2
    vx
    cv
    cG
    cvtxdg
    cfv
    cfv
    cdvds
    wbr
    wn
    vx
    cV
    crab
    chash
    cfv
    #
    cc0
    c2
    cpr
    #
    wcel
    #
    wn
    cG
    ceupth
    cfv
    #
    c0
    wceq
    @2
    c2
    @0
    clt
    wbr
    #
    vx
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsberglem5
    @2
    @0
    cc0
    wceq
    #
    @0
    c2
    wceq
    #
    wo
    @4
    wn
    #
    @0
    cc0
    c2
    elpri
    @5
    @7
    @6
    @5
    @4
    c2
    cc0
    clt
    wbr
    #
    cc0
    c2
    clt
    wbr
    @8
    wn
    2pos
    cc0
    c2
    0re
    2re
    ltnsymi
    ax-mp
    @0
    cc0
    c2
    clt
    breq2
    mtbiri
    @6
    @4
    c2
    c2
    clt
    wbr
    c2
    2re
    ltnri
    @0
    c2
    c2
    clt
    breq2
    mtbiri
    jaoi
    syl
    mt2
    @2
    @3
    c0
    cG
    cupgr
    wcel
    #
    @3
    c0
    wne
    @2
    cG
    cumgr
    wcel
    @9
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergumgr
    cG
    umgrupgr
    ax-mp
    vx
    cG
    cV
    cG
    cvtx
    cfv
    cV
    cE
    cop
    #
    cvtx
    cfv
    #
    cV
    cG
    @10
    cvtx
    konigsberg.g
    fveq2i
    cV
    cvv
    wcel
    cE
    cvv
    cword
    #
    wcel
    @11
    cV
    wceq
    cV
    cc0
    c3
    cfz
    co
    cvv
    konigsberg.v
    cc0
    c3
    cfz
    ovex
    eqeltri
    cE
    cc0
    c1
    cpr
    #
    @1
    cc0
    c3
    cpr
    #
    c1
    c2
    cpr
    #
    @15
    c2
    c3
    cpr
    #
    @16
    cs7
    @12
    konigsberg.e
    @13
    @1
    @14
    @15
    @15
    @16
    @16
    s7cli
    eqeltri
    cE
    cV
    cvv
    @12
    opvtxfv
    mp2an
    eqtr2i
    eulerpath
    mpan
    necon1bi
    ax-mp
end
