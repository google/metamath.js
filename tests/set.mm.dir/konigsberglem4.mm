include "cc0.mm"
include "c2.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "wcel.mm"
include "c1.mm"
include "c3.mm"
include "w3a.mm"
include "ctp.mm"
include "wss.mm"
include "cfz.mm"
include "co.mm"
include "cn0.mm"
include "3nn0.mm"
include "0elfz.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "n2dvds3.mm"
include "konigsberglem1.mm"
include "breq2i.mm"
include "mtbir.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "cle.mm"
include "1nn0.mm"
include "1le3.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "konigsberglem2.mm"
include "3re.mm"
include "leidi.mm"
include "konigsberglem3.mm"
include "3pm3.2i.mm"
include "c0ex.mm"
include "1ex.mm"
include "3ex.mm"
include "tpss.mm"
include "mpbi.mm"

theorem konigsberglem4
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.

  disjoint V x
  disjoint G x
  assert |- { 0 , 1 , 3 } C_ { x e. V | -. 2 || ( ( VtxDeg ` G ) ` x ) }

  proof
    cc0
    c2
    vx
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vx
    cV
    crab
    #
    wcel
    #
    c1
    @5
    wcel
    #
    c3
    @5
    wcel
    #
    w3a
    cc0
    c1
    c3
    ctp
    @5
    wss
    @6
    @7
    @8
    @6
    cc0
    cV
    wcel
    c2
    cc0
    @1
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    cc0
    cc0
    c3
    cfz
    co
    #
    cV
    c3
    cn0
    wcel
    #
    cc0
    @12
    wcel
    3nn0
    c3
    0elfz
    ax-mp
    konigsberg.v
    eleqtrri
    @10
    c2
    c3
    cdvds
    wbr
    #
    n2dvds3
    @9
    c3
    c2
    cdvds
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsberglem1
    breq2i
    mtbir
    @4
    @11
    vx
    cc0
    cV
    @0
    cc0
    wceq
    #
    @3
    @10
    @15
    @2
    @9
    c2
    cdvds
    @0
    cc0
    @1
    fveq2
    breq2d
    notbid
    elrab
    mpbir2an
    @7
    c1
    cV
    wcel
    c2
    c1
    @1
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    c1
    @12
    cV
    c1
    @12
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
    konigsberg.v
    eleqtrri
    @17
    @14
    n2dvds3
    @16
    c3
    c2
    cdvds
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsberglem2
    breq2i
    mtbir
    @4
    @18
    vx
    c1
    cV
    @0
    c1
    wceq
    #
    @3
    @17
    @19
    @2
    @16
    c2
    cdvds
    @0
    c1
    @1
    fveq2
    breq2d
    notbid
    elrab
    mpbir2an
    @8
    c3
    cV
    wcel
    c2
    c3
    @1
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    c3
    @12
    cV
    c3
    @12
    wcel
    @13
    @13
    c3
    c3
    cle
    wbr
    3nn0
    3nn0
    c3
    3re
    leidi
    c3
    c3
    elfz2nn0
    mpbir3an
    konigsberg.v
    eleqtrri
    @21
    @14
    n2dvds3
    @20
    c3
    c2
    cdvds
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsberglem3
    breq2i
    mtbir
    @4
    @22
    vx
    c3
    cV
    @0
    c3
    wceq
    #
    @3
    @21
    @23
    @2
    @20
    c2
    cdvds
    @0
    c3
    @1
    fveq2
    breq2d
    notbid
    elrab
    mpbir2an
    3pm3.2i
    cc0
    c1
    c3
    @5
    c0ex
    1ex
    3ex
    tpss
    mpbi
end
