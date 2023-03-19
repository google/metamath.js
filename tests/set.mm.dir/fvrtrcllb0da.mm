include "crtcl.mm"
include "cn0.mm"
include "dfrtrcl3.mm"
include "cvv.mm"
include "wcel.mm"
include "nn0ex.mm"
include "a1i.mm"
include "cc0.mm"
include "0nn0.mm"
include "fvmptiunrelexplb0da.mm"

theorem fvrtrcllb0da
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvrtrcllb0da.rel: |- ( ph -> Rel R )
  assume fvrtrcllb0da.r: |- ( ph -> R e. _V )


  assert |- ( ph -> ( _I |` U. U. R ) C_ ( t* ` R ) )

  proof
    wph
    crtcl
    cR
    vn
    cn0
    vr
    vn
    vr
    dfrtrcl3
    fvrtrcllb0da.r
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    fvrtrcllb0da.rel
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    fvmptiunrelexplb0da
end
