include "ccnv.mm"
include "wfun.mm"
include "cdif.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "anandir.mm"
include "exbii.mm"
include "19.40.mm"
include "sylbi.mm"
include "wal.mm"
include "nfv.mm"
include "nfe1.mm"
include "nfan.mm"
include "wi.mm"
include "wmo.mm"
include "funmo.mm"
include "vex.mm"
include "brcnv.mm"
include "mobii.mm"
include "sylib.mm"
include "mopick.mm"
include "sylan.mm"
include "con2d.mm"
include "imnan.mm"
include "alrimi.mm"
include "ex.mm"
include "exancom.mm"
include "alnex.mm"
include "3imtr3g.mm"
include "anim2d.mm"
include "syl5.mm"
include "19.29r.mm"
include "sylan2br.mm"
include "wo.mm"
include "andi.mm"
include "ianor.mm"
include "anbi2i.mm"
include "an32.mm"
include "pm3.24.mm"
include "intnan.mm"
include "anass.mm"
include "mtbir.mm"
include "biorfi.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "impbid1.mm"
include "eldif.mm"
include "anbi1i.mm"
include "elima2.mm"
include "notbii.mm"
include "anbi12i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem imadif
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( Fun `' F -> ( F " ( A \ B ) ) = ( ( F " A ) \ ( F " B ) ) )

  proof
    cF
    ccnv
    #
    wfun
    #
    vy
    cF
    cA
    cB
    cdif
    #
    cima
    #
    cF
    cA
    cima
    #
    cF
    cB
    cima
    #
    cdif
    #
    @1
    vx
    cv
    #
    @2
    wcel
    #
    @7
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    wex
    #
    @9
    @4
    wcel
    #
    @9
    @5
    wcel
    #
    wn
    #
    wa
    #
    @9
    @3
    wcel
    @9
    @6
    wcel
    @1
    @7
    cA
    wcel
    #
    @7
    cB
    wcel
    #
    wn
    #
    wa
    #
    @10
    wa
    #
    vx
    wex
    #
    @17
    @10
    wa
    #
    vx
    wex
    #
    @18
    @10
    wa
    #
    vx
    wex
    #
    wn
    #
    wa
    #
    @12
    @16
    @1
    @22
    @28
    @22
    @24
    @19
    @10
    wa
    #
    vx
    wex
    #
    wa
    #
    @1
    @28
    @22
    @23
    @29
    wa
    #
    vx
    wex
    @31
    @21
    @32
    vx
    @17
    @19
    @10
    anandir
    exbii
    @23
    @29
    vx
    19.40
    sylbi
    @1
    @30
    @27
    @24
    @1
    @10
    @19
    wa
    #
    vx
    wex
    #
    @25
    wn
    #
    vx
    wal
    #
    @30
    @27
    @1
    @34
    @36
    @1
    @34
    wa
    #
    @35
    vx
    @1
    @34
    vx
    @1
    vx
    nfv
    @33
    vx
    nfe1
    nfan
    @37
    @18
    @10
    wn
    #
    wi
    @35
    @37
    @10
    @18
    @1
    @10
    vx
    wmo
    #
    @34
    @10
    @19
    wi
    @1
    @9
    @7
    @0
    wbr
    #
    vx
    wmo
    @39
    vx
    @9
    @0
    funmo
    @40
    @10
    vx
    @9
    @7
    cF
    vy
    vex
    #
    vx
    vex
    brcnv
    mobii
    sylib
    @10
    @19
    vx
    mopick
    sylan
    con2d
    @18
    @10
    imnan
    sylib
    alrimi
    ex
    @10
    @19
    vx
    exancom
    @25
    vx
    alnex
    #
    3imtr3g
    anim2d
    syl5
    @28
    @23
    @35
    wa
    #
    vx
    wex
    #
    @22
    @27
    @24
    @36
    @44
    @42
    @23
    @35
    vx
    19.29r
    sylan2br
    @43
    @21
    vx
    @23
    @19
    @38
    wo
    #
    wa
    @23
    @19
    wa
    #
    @23
    @38
    wa
    #
    wo
    #
    @43
    @21
    @23
    @19
    @38
    andi
    @35
    @45
    @23
    @18
    @10
    ianor
    anbi2i
    @21
    @46
    @48
    @17
    @19
    @10
    an32
    @47
    @46
    @47
    @17
    @10
    @38
    wa
    #
    wa
    @49
    @17
    @10
    pm3.24
    intnan
    @17
    @10
    @38
    anass
    mtbir
    biorfi
    bitri
    3bitr4i
    exbii
    sylib
    impbid1
    @11
    @21
    vx
    @8
    @20
    @10
    @7
    cA
    cB
    eldif
    anbi1i
    exbii
    @13
    @24
    @15
    @27
    vx
    @9
    cF
    cA
    @41
    elima2
    @14
    @26
    vx
    @9
    cF
    cB
    @41
    elima2
    notbii
    anbi12i
    3bitr4g
    vx
    @9
    cF
    @2
    @41
    elima2
    @9
    @4
    @5
    eldif
    3bitr4g
    eqrdv
end
