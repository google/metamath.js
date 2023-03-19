include "crcl.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "dfrcl4.mm"
include "cvv.mm"
include "wcel.mm"
include "prex.mm"
include "a1i.mm"
include "1ex.mm"
include "prid2.mm"
include "fvmptiunrelexplb1d.mm"

theorem fvrcllb1d
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvrcllb1d.r: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( r* ` R ) )

  proof
    wph
    crcl
    cR
    vn
    cc0
    c1
    cpr
    #
    vr
    vn
    vr
    dfrcl4
    fvrcllb1d.r
    @0
    cvv
    wcel
    wph
    cc0
    c1
    prex
    a1i
    c1
    @0
    wcel
    wph
    cc0
    c1
    1ex
    prid2
    a1i
    fvmptiunrelexplb1d
end
