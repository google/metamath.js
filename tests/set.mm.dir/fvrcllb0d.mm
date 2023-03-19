include "crcl.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "dfrcl4.mm"
include "cvv.mm"
include "wcel.mm"
include "prex.mm"
include "a1i.mm"
include "c0ex.mm"
include "prid1.mm"
include "fvmptiunrelexplb0d.mm"

theorem fvrcllb0d
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvrcllb0d.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( _I |` ( dom R u. ran R ) ) C_ ( r* ` R ) )

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
    fvrcllb0d.r
    @0
    cvv
    wcel
    wph
    cc0
    c1
    prex
    a1i
    cc0
    @0
    wcel
    wph
    cc0
    c1
    c0ex
    prid1
    a1i
    fvmptiunrelexplb0d
end
