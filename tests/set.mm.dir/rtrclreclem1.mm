include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "crtrcl.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "cmpt.mm"
include "wrex.mm"
include "cc0.mm"
include "wcel.mm"
include "0nn0.mm"
include "ssid.mm"
include "relexp0d.mm"
include "syl5sseqr.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "ssiun.mm"
include "syl.mm"
include "nn0ex.mm"
include "ovex.mm"
include "iunex.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "sseqtr4d.mm"
include "wb.mm"
include "df-rtrclrec.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem rtrclreclem1
  let wph: wff ph
  let cR: class R
  let vr: setvar r
  let vn: setvar n
  assume rtrclreclem.1: |- ( ph -> Rel R )
  assume rtrclreclem.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( _I |` U. U. R ) C_ ( t*rec ` R ) )

  proof
    wph
    cid
    cR
    cuni
    cuni
    cres
    #
    cR
    crtrcl
    cfv
    #
    wss
    #
    wi
    #
    wph
    @0
    cR
    vr
    cvv
    vn
    cn0
    vr
    cv
    #
    vn
    cv
    #
    crelexp
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    wss
    #
    wi
    #
    wph
    @0
    vn
    cn0
    cR
    @5
    crelexp
    co
    #
    ciun
    #
    @9
    wph
    @0
    @12
    wss
    #
    vn
    cn0
    wrex
    #
    @0
    @13
    wss
    wph
    cc0
    cn0
    wcel
    @0
    cR
    cc0
    crelexp
    co
    #
    wss
    #
    @15
    0nn0
    wph
    @0
    @0
    @16
    @0
    ssid
    wph
    cR
    rtrclreclem.1
    rtrclreclem.2
    relexp0d
    syl5sseqr
    @14
    @17
    vn
    cc0
    cn0
    @5
    cc0
    wceq
    @12
    @16
    @0
    @5
    cc0
    cR
    crelexp
    oveq2
    sseq2d
    rspcev
    sylancr
    vn
    cn0
    @12
    @0
    ssiun
    syl
    wph
    cR
    cvv
    wcel
    @13
    cvv
    wcel
    @9
    @13
    wceq
    rtrclreclem.2
    vn
    cn0
    @12
    nn0ex
    cR
    @5
    crelexp
    ovex
    iunex
    vr
    cR
    @7
    @13
    cvv
    cvv
    @8
    @4
    cR
    wceq
    vn
    cn0
    @6
    @12
    @4
    cR
    @5
    crelexp
    oveq1
    iuneq2d
    @8
    eqid
    fvmptg
    sylancl
    sseqtr4d
    crtrcl
    @8
    wceq
    #
    @3
    @11
    wb
    vn
    vr
    df-rtrclrec
    @18
    @2
    @10
    wph
    @18
    @1
    @9
    @0
    cR
    crtrcl
    @8
    fveq1
    sseq2d
    imbi2d
    ax-mp
    mpbir
end
