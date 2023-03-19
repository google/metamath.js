include "crtcl.mm"
include "cn0.mm"
include "dfrtrcl3.mm"
include "cvv.mm"
include "wcel.mm"
include "nn0ex.mm"
include "a1i.mm"
include "c1.mm"
include "1nn0.mm"
include "fvmptiunrelexplb1d.mm"

theorem fvrtrcllb1d
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvrtrcllb1d.r: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( t* ` R ) )

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
    fvrtrcllb1d.r
    cn0
    cvv
    wcel
    wph
    nn0ex
    a1i
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    fvmptiunrelexplb1d
end
