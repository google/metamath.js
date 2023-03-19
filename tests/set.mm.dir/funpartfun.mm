include "cfunpart.mm"
include "wfun.mm"
include "cimage.mm"
include "csingle.mm"
include "ccom.mm"
include "cvv.mm"
include "csingles.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "cres.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "relres.mm"
include "wcel.mm"
include "vex.mm"
include "brres.mm"
include "simplbi.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wex.mm"
include "ancom.mm"
include "funpartlem.mm"
include "anbi1i.mm"
include "bitri.mm"
include "cop.mm"
include "df-br.mm"
include "anbi12i.mm"
include "elimasn.mm"
include "bitr4i.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "velsn.mm"
include "equtr2.mm"
include "syl2anb.mm"
include "syl6bi.mm"
include "syl5bi.mm"
include "exlimiv.mm"
include "impl.mm"
include "sylanb.mm"
include "sylan2.mm"
include "gen2.mm"
include "ax-gen.mm"
include "df-funpart.mm"
include "funeqi.mm"
include "dffun2.mm"
include "mpbir2an.mm"

theorem funpartfun
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- Fun Funpart F

  proof
    cF
    cfunpart
    #
    wfun
    #
    cF
    cF
    cimage
    csingle
    ccom
    cvv
    csingles
    cxp
    cin
    cdm
    #
    cres
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    wbr
    #
    @5
    vz
    cv
    #
    @3
    wbr
    #
    wa
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    #
    cF
    @2
    relres
    @12
    vx
    @11
    vy
    vz
    @9
    @7
    @5
    @8
    cF
    wbr
    #
    @10
    @9
    @14
    @5
    @2
    wcel
    #
    @5
    @8
    cF
    @2
    vz
    vex
    #
    brres
    simplbi
    @7
    cF
    @5
    csn
    cima
    #
    vw
    cv
    #
    csn
    #
    wceq
    #
    vw
    wex
    #
    @5
    @6
    cF
    wbr
    #
    wa
    #
    @14
    @10
    @7
    @22
    @15
    wa
    #
    @23
    @5
    @6
    cF
    @2
    vy
    vex
    #
    brres
    @24
    @15
    @22
    wa
    @23
    @22
    @15
    ancom
    @15
    @21
    @22
    vw
    @5
    cF
    funpartlem
    anbi1i
    bitri
    bitri
    @21
    @22
    @14
    @10
    @20
    @22
    @14
    wa
    #
    @10
    wi
    vw
    @26
    @6
    @17
    wcel
    #
    @8
    @17
    wcel
    #
    wa
    #
    @20
    @10
    @26
    @5
    @6
    cop
    cF
    wcel
    #
    @5
    @8
    cop
    cF
    wcel
    #
    wa
    @29
    @22
    @30
    @14
    @31
    @5
    @6
    cF
    df-br
    @5
    @8
    cF
    df-br
    anbi12i
    @27
    @30
    @28
    @31
    cF
    @5
    @6
    vx
    vex
    #
    @25
    elimasn
    cF
    @5
    @8
    @32
    @16
    elimasn
    anbi12i
    bitr4i
    @20
    @29
    @6
    @19
    wcel
    #
    @8
    @19
    wcel
    #
    wa
    @10
    @20
    @27
    @33
    @28
    @34
    @17
    @19
    @6
    eleq2
    @17
    @19
    @8
    eleq2
    anbi12d
    @33
    vy
    vw
    weq
    vz
    vw
    weq
    @10
    @34
    vy
    @18
    velsn
    vz
    @18
    velsn
    vy
    vz
    vw
    equtr2
    syl2anb
    syl6bi
    syl5bi
    exlimiv
    impl
    sylanb
    sylan2
    gen2
    ax-gen
    @1
    @3
    wfun
    @4
    @13
    wa
    @0
    @3
    cF
    df-funpart
    funeqi
    vx
    vy
    vz
    @3
    dffun2
    bitri
    mpbir2an
end
