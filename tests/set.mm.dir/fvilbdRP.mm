include "cid.mm"
include "c1.mm"
include "csn.mm"
include "dfid6.mm"
include "cvv.mm"
include "wcel.mm"
include "snex.mm"
include "a1i.mm"
include "1ex.mm"
include "snid.mm"
include "fvmptiunrelexplb1d.mm"

theorem fvilbdRP
  let wph: wff ph
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume fvilbdRP.r: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( _I ` R ) )

  proof
    wph
    cid
    cR
    vn
    c1
    csn
    #
    vr
    vr
    vn
    dfid6
    fvilbdRP.r
    @0
    cvv
    wcel
    wph
    c1
    snex
    a1i
    c1
    @0
    wcel
    wph
    c1
    1ex
    snid
    a1i
    fvmptiunrelexplb1d
end
