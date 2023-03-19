include "ccnv.mm"
include "cpred.mm"
include "cinf.mm"
include "wbr.mm"
include "cwsuc.mm"
include "wcel.mm"
include "wn.mm"
include "wb.mm"
include "brcnvg.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elpredg.mm"
include "wwe.mm"
include "wor.mm"
include "weso.mm"
include "syl.mm"
include "cv.mm"
include "wrex.mm"
include "breq2.mm"
include "rspcev.mm"
include "wsuclem.mm"
include "inflb.mm"
include "mpd.mm"
include "df-wsuc.mm"
include "breq2i.mm"
include "sylnibr.mm"

theorem wsuclb
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume wsuclb.1: |- ( ph -> R We A )
  assume wsuclb.2: |- ( ph -> R Se A )
  assume wsuclb.3: |- ( ph -> X e. V )
  assume wsuclb.4: |- ( ph -> Y e. A )
  assume wsuclb.5: |- ( ph -> X R Y )


  assert |- ( ph -> -. Y R wsuc ( R , A , X ) )

  proof
    wph
    cY
    cA
    cR
    ccnv
    #
    cX
    cpred
    #
    cA
    cR
    cinf
    #
    cR
    wbr
    #
    cY
    cA
    cR
    cX
    cwsuc
    #
    cR
    wbr
    wph
    cY
    @1
    wcel
    #
    @3
    wn
    wph
    @5
    cY
    cX
    @0
    wbr
    #
    wph
    @6
    cX
    cY
    cR
    wbr
    #
    wsuclb.5
    wph
    cY
    cA
    wcel
    #
    cX
    cV
    wcel
    #
    @6
    @7
    wb
    wsuclb.4
    wsuclb.3
    cY
    cX
    cA
    cV
    cR
    brcnvg
    syl2anc
    mpbird
    wph
    @9
    @8
    @5
    @6
    wb
    wsuclb.3
    wsuclb.4
    cA
    cV
    @0
    cX
    cY
    elpredg
    syl2anc
    mpbird
    wph
    va
    vb
    vc
    cA
    @1
    cY
    cR
    wph
    cA
    cR
    wwe
    cA
    cR
    wor
    wsuclb.1
    cA
    cR
    weso
    syl
    wph
    va
    vb
    vc
    vy
    cA
    cR
    cV
    cX
    wsuclb.1
    wsuclb.2
    wsuclb.3
    wph
    @8
    @7
    cX
    vy
    cv
    #
    cR
    wbr
    #
    vy
    cA
    wrex
    wsuclb.4
    wsuclb.5
    @11
    @7
    vy
    cY
    cA
    @10
    cY
    cX
    cR
    breq2
    rspcev
    syl2anc
    wsuclem
    inflb
    mpd
    @4
    @2
    cY
    cR
    cA
    cR
    cX
    df-wsuc
    breq2i
    sylnibr
end
