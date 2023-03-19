include "wbr.mm"
include "wor.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "sotr.mm"
include "syl13anc.mm"
include "mp2and.mm"

theorem sotrd
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume sotrd.1: |- ( ph -> R Or A )
  assume sotrd.2: |- ( ph -> X e. A )
  assume sotrd.3: |- ( ph -> Y e. A )
  assume sotrd.4: |- ( ph -> Z e. A )
  assume sotrd.5: |- ( ph -> X R Y )
  assume sotrd.6: |- ( ph -> Y R Z )


  assert |- ( ph -> X R Z )

  proof
    wph
    cX
    cY
    cR
    wbr
    #
    cY
    cZ
    cR
    wbr
    #
    cX
    cZ
    cR
    wbr
    #
    sotrd.5
    sotrd.6
    wph
    cA
    cR
    wor
    cX
    cA
    wcel
    cY
    cA
    wcel
    cZ
    cA
    wcel
    @0
    @1
    wa
    @2
    wi
    sotrd.1
    sotrd.2
    sotrd.3
    sotrd.4
    cA
    cX
    cY
    cZ
    cR
    sotr
    syl13anc
    mp2and
end
