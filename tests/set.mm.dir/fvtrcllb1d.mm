include "ctcl.mm"
include "cn.mm"
include "dftrcl3.mm"
include "cvv.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "c1.mm"
include "1nn.mm"
include "fvmptiunrelexplb1d.mm"

theorem fvtrcllb1d
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvtrcllb1d.r: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( t+ ` R ) )

  proof
    wph
    ctcl
    cR
    vn
    cn
    vr
    vn
    vr
    dftrcl3
    fvtrcllb1d.r
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    c1
    cn
    wcel
    wph
    1nn
    a1i
    fvmptiunrelexplb1d
end
