include "cuz.mm"
include "crn.mm"
include "cz.mm"
include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "wf.mm"
include "uzf.mm"
include "frn.mm"
include "ax-mp.mm"
include "c1.mm"
include "wfn.mm"
include "ffn.mm"
include "1z.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "ne0ii.mm"
include "wceq.mm"
include "wrex.mm"
include "wn.mm"
include "uzid.mm"
include "n0i.mm"
include "syl.mm"
include "nrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "mtbir.mm"
include "nelir.mm"
include "wa.mm"
include "uzin2.mm"
include "vex.mm"
include "inex1.mm"
include "pwid.mm"
include "inelcm.mm"
include "sylancl.mm"
include "rgen2a.mm"
include "3pm3.2i.mm"
include "cvv.mm"
include "zex.mm"
include "isfbas.mm"
include "mpbir2an.mm"

theorem zfbas
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cZ: class Z


  assert |- ran ZZ>= e. ( fBas ` ZZ )

  proof
    cuz
    crn
    #
    cz
    cfbas
    cfv
    wcel
    #
    @0
    cz
    cpw
    #
    wss
    #
    @0
    c0
    wne
    #
    c0
    @0
    wnel
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cpw
    #
    cin
    c0
    wne
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    w3a
    #
    cz
    @2
    cuz
    wf
    #
    @3
    uzf
    cz
    @2
    cuz
    frn
    ax-mp
    @4
    @5
    @11
    c1
    cuz
    cfv
    #
    @0
    cuz
    cz
    wfn
    #
    c1
    cz
    wcel
    @14
    @0
    wcel
    @13
    @15
    uzf
    cz
    @2
    cuz
    ffn
    ax-mp
    #
    1z
    cz
    c1
    cuz
    fnfvelrn
    mp2an
    ne0ii
    c0
    @0
    c0
    @0
    wcel
    #
    @6
    cuz
    cfv
    #
    c0
    wceq
    #
    vx
    cz
    wrex
    #
    @19
    vx
    cz
    @6
    cz
    wcel
    @6
    @18
    wcel
    @19
    wn
    @6
    uzid
    @18
    @6
    n0i
    syl
    nrex
    @15
    @17
    @20
    wb
    @16
    vx
    cz
    c0
    cuz
    fvelrnb
    ax-mp
    mtbir
    nelir
    @10
    vx
    vy
    @0
    @6
    @0
    wcel
    @7
    @0
    wcel
    wa
    @8
    @0
    wcel
    @8
    @9
    wcel
    @10
    @6
    @7
    uzin2
    @8
    @6
    @7
    vx
    vex
    inex1
    pwid
    @8
    @0
    @9
    inelcm
    sylancl
    rgen2a
    3pm3.2i
    cz
    cvv
    wcel
    @1
    @3
    @12
    wa
    wb
    zex
    vx
    vy
    cvv
    cz
    @0
    isfbas
    ax-mp
    mpbir2an
end
