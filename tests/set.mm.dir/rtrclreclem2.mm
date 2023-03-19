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
include "c1.mm"
include "wcel.mm"
include "1nn0.mm"
include "ssid.mm"
include "a1i.mm"
include "relexp1d.mm"
include "sseqtr4d.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "ssiun.mm"
include "syl.mm"
include "eqidd.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "adantl.mm"
include "nn0ex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmptd.mm"
include "wb.mm"
include "df-rtrclrec.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem rtrclreclem2
  let wph: wff ph
  let cR: class R
  let vr: setvar r
  let vn: setvar n
  assume rtrclreclem.ex: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( t*rec ` R ) )

  proof
    wph
    cR
    cR
    crtrcl
    cfv
    #
    wss
    #
    wi
    #
    wph
    cR
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
    cR
    vn
    cn0
    cR
    @4
    crelexp
    co
    #
    ciun
    #
    @8
    wph
    cR
    @11
    wss
    #
    vn
    cn0
    wrex
    #
    cR
    @12
    wss
    wph
    c1
    cn0
    wcel
    cR
    cR
    c1
    crelexp
    co
    #
    wss
    #
    @14
    1nn0
    wph
    cR
    cR
    @15
    cR
    cR
    wss
    wph
    cR
    ssid
    a1i
    wph
    cR
    rtrclreclem.ex
    relexp1d
    sseqtr4d
    @13
    @16
    vn
    c1
    cn0
    @4
    c1
    wceq
    @11
    @15
    cR
    @4
    c1
    cR
    crelexp
    oveq2
    sseq2d
    rspcev
    sylancr
    vn
    cn0
    @11
    cR
    ssiun
    syl
    wph
    vr
    cR
    @6
    @12
    cvv
    @7
    cvv
    wph
    @7
    eqidd
    @3
    cR
    wceq
    #
    @6
    @12
    wceq
    wph
    @17
    vn
    cn0
    @5
    @11
    @3
    cR
    @4
    crelexp
    oveq1
    iuneq2d
    adantl
    rtrclreclem.ex
    @12
    cvv
    wcel
    wph
    vn
    cn0
    @11
    nn0ex
    cR
    @4
    crelexp
    ovex
    iunex
    a1i
    fvmptd
    sseqtr4d
    crtrcl
    @7
    wceq
    #
    @2
    @10
    wb
    vn
    vr
    df-rtrclrec
    @18
    @1
    @9
    wph
    @18
    @0
    @8
    cR
    cR
    crtrcl
    @7
    fveq1
    sseq2d
    imbi2d
    ax-mp
    mpbir
end
