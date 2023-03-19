include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "ctb.mm"
include "wcel.mm"
include "cvv.mm"
include "cun.mm"
include "wss.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "snex.mm"
include "unexg.mm"
include "mpan2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "elex.mm"
include "cv.mm"
include "cin.mm"
include "cpw.mm"
include "cuni.mm"
include "wral.mm"
include "wb.mm"
include "indif1.mm"
include "unieqi.mm"
include "unidif0.mm"
include "eqtri.mm"
include "sseq2i.mm"
include "ralbii.mm"
include "inss2.mm"
include "wceq.mm"
include "sseli.mm"
include "elsni.mm"
include "syl.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "rgen.mm"
include "ralunb.mm"
include "mpbiran.mm"
include "inundif.mm"
include "raleqi.mm"
include "3bitr2i.mm"
include "inss1.mm"
include "ralrimivw.mm"
include "a1i.mm"
include "difexg.mm"
include "isbasisg.mm"
include "3bitr4d.mm"
include "pm5.21nii.mm"

theorem basdif0
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( B \ { (/) } ) e. TopBases <-> B e. TopBases )

  proof
    cB
    c0
    csn
    #
    cdif
    #
    ctb
    wcel
    #
    cB
    cvv
    wcel
    #
    cB
    ctb
    wcel
    #
    @2
    cB
    @1
    @0
    cun
    #
    wss
    @5
    cvv
    wcel
    #
    @3
    cB
    cB
    @0
    cun
    @5
    cB
    @0
    ssun1
    cB
    @0
    undif1
    sseqtr4i
    @2
    @0
    cvv
    wcel
    @6
    c0
    snex
    @1
    @0
    ctb
    cvv
    unexg
    mpan2
    cB
    @5
    cvv
    ssexg
    sylancr
    cB
    ctb
    elex
    @3
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    @1
    @9
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @9
    cB
    @10
    cin
    #
    cuni
    #
    wss
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @2
    @4
    @15
    @20
    wb
    @3
    @15
    @19
    vx
    @1
    wral
    #
    @19
    vx
    cB
    @0
    cin
    #
    @1
    cun
    #
    wral
    #
    @20
    @14
    @19
    vx
    @1
    @14
    @18
    vy
    @1
    wral
    #
    @18
    vy
    @23
    wral
    #
    @19
    @13
    @18
    vy
    @1
    @12
    @17
    @9
    @12
    @16
    @0
    cdif
    #
    cuni
    @17
    @11
    @27
    cB
    @10
    @0
    indif1
    unieqi
    @16
    unidif0
    eqtri
    sseq2i
    ralbii
    @26
    @18
    vy
    @22
    wral
    @25
    @18
    vy
    @22
    @8
    @22
    wcel
    #
    @9
    @8
    @17
    @7
    @8
    inss2
    @28
    @8
    c0
    @17
    @28
    @8
    @0
    wcel
    @8
    c0
    wceq
    @22
    @0
    @8
    cB
    @0
    inss2
    #
    sseli
    @8
    c0
    elsni
    syl
    @17
    0ss
    #
    syl6eqss
    syl5ss
    rgen
    @18
    vy
    @22
    @1
    ralunb
    mpbiran
    @18
    vy
    @23
    cB
    cB
    @0
    inundif
    #
    raleqi
    3bitr2i
    ralbii
    @24
    @19
    vx
    @22
    wral
    @21
    @19
    vx
    @22
    @7
    @22
    wcel
    #
    @18
    vy
    cB
    @32
    @9
    @7
    @17
    @7
    @8
    inss1
    @32
    @7
    c0
    @17
    @32
    @7
    @0
    wcel
    @7
    c0
    wceq
    @22
    @0
    @7
    @29
    sseli
    @7
    c0
    elsni
    syl
    @30
    syl6eqss
    syl5ss
    ralrimivw
    rgen
    @19
    vx
    @22
    @1
    ralunb
    mpbiran
    @19
    vx
    @23
    cB
    @31
    raleqi
    3bitr2i
    a1i
    @3
    @1
    cvv
    wcel
    @2
    @15
    wb
    cB
    @0
    cvv
    difexg
    vx
    vy
    @1
    cvv
    isbasisg
    syl
    vx
    vy
    cB
    cvv
    isbasisg
    3bitr4d
    pm5.21nii
end
