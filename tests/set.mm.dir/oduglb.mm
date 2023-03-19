include "wcel.mm"
include "club.mm"
include "cfv.mm"
include "cglb.mm"
include "cbs.mm"
include "cpw.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "ccnv.mm"
include "wb.mm"
include "vex.mm"
include "brcnv.mm"
include "ralbii.mm"
include "imbi12i.mm"
include "anbi12i.mm"
include "a1i.mm"
include "riotabiia.mm"
include "mpteq2i.mm"
include "reubii.mm"
include "abbii.mm"
include "reseq12i.mm"
include "eqcomi.mm"
include "eqid.mm"
include "biid.mm"
include "id.mm"
include "lubfval.mm"
include "cvv.mm"
include "wceq.mm"
include "codu.mm"
include "fvex.mm"
include "eqeltri.mm"
include "odubas.mm"
include "oduleval.mm"
include "glbfval.mm"
include "mp1i.mm"
include "3eqtr4a.mm"
include "syl5eq.mm"

theorem oduglb
  let cD: class D
  let cU: class U
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cL: class L
  let c.or: class .\/
  let c.an: class ./\
  assume oduglb.d: |- D = ( ODual ` O )
  assume oduglb.l: |- U = ( lub ` O )


  assert |- ( O e. V -> U = ( glb ` D ) )

  proof
    cO
    cV
    wcel
    #
    cU
    cO
    club
    cfv
    #
    cD
    cglb
    cfv
    #
    oduglb.l
    @0
    va
    cO
    cbs
    cfv
    #
    cpw
    #
    vc
    cv
    #
    vb
    cv
    #
    cO
    cple
    cfv
    #
    wbr
    #
    vc
    va
    cv
    #
    wral
    #
    @5
    vd
    cv
    #
    @7
    wbr
    #
    vc
    @9
    wral
    #
    @6
    @11
    @7
    wbr
    #
    wi
    #
    vd
    @3
    wral
    #
    wa
    #
    vb
    @3
    crio
    #
    cmpt
    #
    @17
    vb
    @3
    wreu
    #
    va
    cab
    #
    cres
    #
    va
    @4
    @6
    @5
    @7
    ccnv
    #
    wbr
    #
    vc
    @9
    wral
    #
    @11
    @5
    @23
    wbr
    #
    vc
    @9
    wral
    #
    @11
    @6
    @23
    wbr
    #
    wi
    #
    vd
    @3
    wral
    #
    wa
    #
    vb
    @3
    crio
    #
    cmpt
    #
    @31
    vb
    @3
    wreu
    #
    va
    cab
    #
    cres
    #
    @1
    @2
    @36
    @22
    @33
    @19
    @35
    @21
    va
    @4
    @32
    @18
    @31
    @17
    vb
    @3
    @31
    @17
    wb
    @6
    @3
    wcel
    @25
    @10
    @30
    @16
    @24
    @8
    vc
    @9
    @6
    @5
    @7
    vb
    vex
    #
    vc
    vex
    #
    brcnv
    ralbii
    @29
    @15
    vd
    @3
    @27
    @13
    @28
    @14
    @26
    @12
    vc
    @9
    @11
    @5
    @7
    vd
    vex
    #
    @38
    brcnv
    ralbii
    @11
    @6
    @7
    @39
    @37
    brcnv
    imbi12i
    ralbii
    anbi12i
    #
    a1i
    riotabiia
    mpteq2i
    @34
    @20
    va
    @31
    @17
    vb
    @3
    @40
    reubii
    abbii
    reseq12i
    eqcomi
    @0
    @17
    vb
    vc
    vd
    @3
    @1
    cO
    @7
    cV
    va
    @3
    eqid
    #
    @7
    eqid
    #
    @1
    eqid
    @17
    biid
    @0
    id
    lubfval
    cD
    cvv
    wcel
    #
    @2
    @36
    wceq
    @0
    cD
    cO
    codu
    cfv
    cvv
    oduglb.d
    cO
    codu
    fvex
    eqeltri
    @43
    @31
    vb
    vc
    vd
    @3
    @2
    cD
    @23
    cvv
    va
    @3
    cD
    cO
    oduglb.d
    @41
    odubas
    cD
    @7
    cO
    oduglb.d
    @42
    oduleval
    @2
    eqid
    @31
    biid
    @43
    id
    glbfval
    mp1i
    3eqtr4a
    syl5eq
end
